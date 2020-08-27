package org.arend.lib.meta;

import org.arend.ext.concrete.*;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.body.CoreBody;
import org.arend.ext.core.body.CoreElimBody;
import org.arend.ext.core.body.CoreElimClause;
import org.arend.ext.core.body.CorePattern;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.*;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Pair;
import org.arend.lib.util.PatternUtils;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class MatchingCasesMeta extends BaseMetaDefinition implements MetaResolver {
  private final StdExtension ext;

  public MatchingCasesMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false, true, true };
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    if (args.size() > 2) {
      resolver.getErrorReporter().report(new NameResolverError("Expected at most 2 arguments", contextData.getMarker()));
      return null;
    }
    if (args.size() == 2 && !(!args.get(0).isExplicit() && args.get(1).isExplicit())) {
      resolver.getErrorReporter().report(new NameResolverError("Expected 1 implicit and 1 explicit argument", contextData.getMarker()));
      return null;
    }

    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    ConcreteAppBuilder builder = factory.appBuilder(contextData.getReferenceExpression());
    if (!args.isEmpty() && !args.get(0).isExplicit()) {
      builder.app(resolver.resolve(args.get(0).getExpression()), args.get(0).isExplicit());
    }
    builder.app(resolver.resolve(factory.caseExpr(false, Collections.emptyList(), null, null, contextData.getClauses() == null ? Collections.emptyList() : contextData.getClauses().getClauseList())));
    if (args.size() == 1 && args.get(0).isExplicit()) {
      builder.app(resolver.resolve(args.get(0).getExpression()));
    } else if (args.size() > 1) {
      builder.app(resolver.resolve(args.get(1).getExpression()));
    }
    return builder.build();
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteExpression marker = contextData.getMarker();
    ConcreteFactory factory = ext.factory.withData(marker);
    List<CoreElimBody> bodies = new ArrayList<>();
    List<Integer> bodySizes = new ArrayList<>(); // bodySizes[i] is the number of parameters of bodies[i]
    List<CoreParameter> bodyParameters = new ArrayList<>(); // bodyParameters[i] is the parameters of bodies[i]
    List<CoreExpression> subexpressions = new ArrayList<>(); // found occurrences of \case expressions or defCalls
    List<CoreExpression> subexpressionTypes = new ArrayList<>(); // their types
    List<List<TypedExpression>> subexpressionArgs = new ArrayList<>();
    CoreExpression expectedType = contextData.getExpectedType().normalize(NormalizationMode.RNF);
    boolean[] isSCase = new boolean[] { false };
    List<List<List<? extends CorePattern>>> requiredBlocks = new ArrayList<>();
    List<List<List<CorePattern>>> refinedBlocks = new ArrayList<>();

    // Parse parameters
    Set<Integer> caseOccurrences; // we are looking for \case expressions if caseOccurrences is either null or non-empty
    Map<CoreFunctionDefinition, Integer> defCount = new HashMap<>(); // if defCount.get(def) != null, then we are looking for def
    Map<CoreFunctionDefinition, Set<Integer>> defOccurrences = new HashMap<>(); // if we are looking for def and defOccurrences.get(def) == null, then we are looking for all occurrences; otherwise only for the specified ones; defOccurrences.get(def) is never empty
    if (!args.get(0).isExplicit()) {
      List<? extends ConcreteExpression> params = Utils.getArgumentList(args.get(0).getExpression());
      if (params.isEmpty()) {
        errorReporter.report(new IgnoredArgumentError(args.get(0).getExpression()));
        caseOccurrences = null;
      } else {
        List<List<? extends ConcreteExpression>> lists = new ArrayList<>();
        List<ConcreteExpression> defList = new ArrayList<>();
        for (ConcreteExpression param : params) {
          if (param instanceof ConcreteTupleExpression) {
            lists.add(Utils.getArgumentList(param));
          } else {
            defList.add(param);
          }
        }
        if (!defList.isEmpty()) {
          lists.add(defList);
        }

        Set<Integer> myCaseOccurrences = new HashSet<>();
        for (List<? extends ConcreteExpression> list : lists) {
          Set<Integer> occurrences = new HashSet<>();
          for (ConcreteExpression param : list) {
            if (param instanceof ConcreteNumberExpression) {
              occurrences.add(((ConcreteNumberExpression) param).getNumber().intValue());
            } else if (!(param instanceof ConcreteReferenceExpression)) {
              errorReporter.report(new TypecheckingError("Unrecognized parameter", param));
            }
          }
          boolean isCase = true;
          for (ConcreteExpression param : list) {
            if (param instanceof ConcreteReferenceExpression) {
              CoreDefinition def = ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) param).getReferent());
              if (def instanceof CoreFunctionDefinition && ((CoreFunctionDefinition) def).getBody() instanceof CoreElimBody) {
                isCase = false;
                if (defCount.putIfAbsent((CoreFunctionDefinition) def, 0) == null) {
                  if (!occurrences.isEmpty()) {
                    defOccurrences.put((CoreFunctionDefinition) def, occurrences);
                  }
                } else {
                  errorReporter.report(new IgnoredArgumentError("Parameters for '" + def.getName() + "' are already specified", param));
                }
              } else {
                errorReporter.report(new TypecheckingError("Expected a function defined by pattern matching", param));
              }
            }
          }
          if (isCase) {
            if (myCaseOccurrences != null && myCaseOccurrences.isEmpty()) {
              myCaseOccurrences = occurrences.isEmpty() ? null : occurrences;
            } else {
              errorReporter.report(new IgnoredArgumentError("Parameters for \\case expressions are already specified", list.isEmpty() ? args.get(0).getExpression() : list.get(0)));
            }
          }
        }
        caseOccurrences = myCaseOccurrences;
      }
    } else {
      caseOccurrences = null;
    }

    // Find subexpressions
    int[] caseCount = { 0 };
    expectedType.findSubexpression(expr -> {
      Collection<? extends CoreExpression> matchArgs = null;
      CoreElimBody body = null;
      CoreParameter parameters = null;
      if (expr instanceof CoreCaseExpression && (caseOccurrences == null || caseOccurrences.remove(++caseCount[0]))) {
        CoreCaseExpression caseExpr = (CoreCaseExpression) expr;
        if (caseExpr.isSCase()) {
          isSCase[0] = true;
        }
        matchArgs = caseExpr.getArguments();
        body = caseExpr.getElimBody();
        parameters = caseExpr.getParameters();
      } else if (expr instanceof CoreFunCallExpression) {
        CoreFunctionDefinition def = ((CoreFunCallExpression) expr).getDefinition();
        Integer count = defCount.get(def);
        if (count != null) {
          Set<Integer> occurrences = defOccurrences.get(def);
          if (occurrences == null || occurrences.contains(count + 1)) {
            CoreBody body1 = def.getBody();
            if (body1 instanceof CoreElimBody) {
              if (def.getKind() == CoreFunctionDefinition.Kind.SFUNC) {
                isSCase[0] = true;
              }
              matchArgs = ((CoreFunCallExpression) expr).getDefCallArguments();
              body = (CoreElimBody) body1;
              parameters = def.getParameters();
            }
          }
          if (occurrences != null) {
            defCount.put(def, count + 1);
          }
        }
      }

      if (matchArgs != null) {
        bodies.add(body);
        bodySizes.add(matchArgs.size());
        bodyParameters.add(parameters);
        subexpressions.add(expr);
        subexpressionTypes.add(expr.computeType());
        List<TypedExpression> typedArgs = new ArrayList<>(matchArgs.size());
        for (CoreExpression argument : matchArgs) {
          if (!(argument instanceof CoreCaseExpression) || caseOccurrences != null) {
            typedArgs.add(argument.computeTyped());
          }
        }
        subexpressionArgs.add(typedArgs);

        List<List<? extends CorePattern>> block = new ArrayList<>();
        for (CoreElimClause clause : body.getClauses()) {
          block.add(clause.getPatterns());
        }
        requiredBlocks.add(block);
        refinedBlocks.add(body.computeRefinedPatterns(parameters));
        return caseOccurrences != null && caseOccurrences.isEmpty() && defCount.isEmpty();
      }

      return false;
    });

    CoreParameter caseParams; {
      List<CoreExpression> caseTypes = new ArrayList<>();
      for (List<TypedExpression> list : subexpressionArgs) {
        for (TypedExpression typed : list) {
          caseTypes.add(typed.getType());
        }
      }
      if (caseTypes.isEmpty()) {
        errorReporter.report(new TypecheckingError("Cannot find matching subexpressions", contextData.getMarker()));
        return null;
      }
      caseParams = typechecker.makeParameters(caseTypes, marker);
    }

    int caseParam = args.get(0).isExplicit() ? 0 : 1;
    List<? extends ConcreteClause> actualClauses = ((ConcreteCaseExpression) args.get(caseParam).getExpression()).getClauses();
    List<List<CorePattern>> actualRows = new ArrayList<>();
    if (!actualClauses.isEmpty()) {
      boolean ok = true;
      int s = Utils.parametersSize(caseParams);
      for (ConcreteClause clause : actualClauses) {
        if (clause.getPatterns().size() != s) {
          errorReporter.report(new TypecheckingError("Expected " + s + " patterns", clause));
          ok = false;
          continue;
        }
        List<CorePattern> row = typechecker.typecheckPatterns(clause.getPatterns(), caseParams, clause);
        if (row == null) {
          ok = false;
          continue;
        }
        actualRows.add(row);
      }
      if (!ok) {
        return null;
      }
    }

    // Typecheck the result type
    List<ArendRef> subexpressionRefs = new ArrayList<>(subexpressionTypes.size());
    List<ConcreteParameter> resultLambdaParams = new ArrayList<>(subexpressionTypes.size());
    for (CoreExpression type : subexpressionTypes) {
      ArendRef ref = factory.local(ext.renamerFactory.getNameFromType(type, null));
      subexpressionRefs.add(ref);
      resultLambdaParams.add(factory.param(ref));
    }
    ConcreteExpression caseResult = factory.meta("case_return_lambda", new ReplaceSubexpressionsMeta(expectedType, subexpressions, subexpressionRefs));
    TypedExpression resultLambda = resultLambdaParams.isEmpty() ? typechecker.typecheck(caseResult, null) : typechecker.typecheckLambda(factory.lam(resultLambdaParams, caseResult), typechecker.makeParameters(subexpressionTypes, marker));
    if (resultLambda == null) {
      return null;
    }

    // Find coverings of required rows by actual rows
    List<List<CorePattern>> requiredBlock = product(requiredBlocks);
    List<List<CorePattern>> refinedBlock = product(refinedBlocks);
    Map<Integer, List<Integer>> coveringRows = new HashMap<>(); // keys are indexing requiredBlock, values are indexing actualRows
    for (int i = 0; i < requiredBlock.size(); i++) {
      List<Integer> covering = PatternUtils.computeCovering(actualRows, requiredBlock.get(i));
      if (covering != null) {
        coveringRows.put(i, covering);
      }
    }

    // If there is no default expression and not all rows are covered, report them and quit
    if (caseParam + 1 >= args.size() && coveringRows.size() < requiredBlock.size()) {
      List<List<CorePattern>> missingRows = new ArrayList<>();
      for (int i = 0; i < requiredBlock.size(); i++) {
        if (!coveringRows.containsKey(i)) {
          missingRows.add(requiredBlock.get(i));
        }
      }
      errorReporter.report(new MissingClausesError(missingRows, caseParams, Collections.emptyList(), false, marker));
      return null;
    }

    // Add not covered clauses to actual clauses
    if (coveringRows.size() == requiredBlock.size()) {
      if (caseParam + 1 < args.size()) {
        errorReporter.report(new IgnoredArgumentError(args.get(caseParam + 1).getExpression()));
      }
    } else {
      for (int i = 0; i < requiredBlock.size(); i++) {
        if (!coveringRows.containsKey(i)) {
          actualRows.add(requiredBlock.get(i));
        }
      }
    }

    // Find actual rows that cover refined rows
    Map<Integer, Integer> actualUsages = new HashMap<>(); // keys are indexing actualRows
    List<List<CorePattern>> refinedRows = new ArrayList<>();
    List<Pair<Integer, Map<CoreBinding, CorePattern>>> refinedToActual = new ArrayList<>(); // indices of this list = indices of refinedRows, and refinedToActual[i].proj1 indexing actualRows
    for (List<CorePattern> refinedRow : refinedBlock) {
      for (int i = 0, j = actualClauses.size(); i < requiredBlock.size(); i++) {
        List<Integer> covering = coveringRows.get(i);
        Map<CoreBinding, CorePattern> subst1 = new HashMap<>();
        Map<CoreBinding, CorePattern> subst2 = new HashMap<>();
        // This conditions is equivalent to PatternUtils.refines(refinedRow, requiredBlock.get(i))
        if (PatternUtils.unify(refinedRow, requiredBlock.get(i), subst1, subst2) && PatternUtils.isTrivial(subst1.values())) {
          if (covering == null) {
            boolean trivial = PatternUtils.isTrivial(subst2.values());
            actualUsages.compute(j, (k, v) -> v == null ? 1 : v + 1);
            refinedToActual.add(new Pair<>(j, trivial ? Collections.emptyMap() : subst2));
            refinedRows.add(refinedRow);
          } else {
            // here we need to further refine refinedRow
            for (Integer index : covering) {
              Map<CoreBinding, CorePattern> subst3 = new HashMap<>();
              Map<CoreBinding, CorePattern> subst4 = new HashMap<>();
              if (PatternUtils.unify(refinedRow, actualRows.get(index), subst3, subst4)) {
                boolean trivial = PatternUtils.isTrivial(subst4.values());
                actualUsages.compute(index, (k, v) -> v == null ? 1 : v + 1);
                refinedToActual.add(new Pair<>(index, trivial ? Collections.emptyMap() : subst4));
                subst3.entrySet().removeIf(e -> e.getValue().getBinding() != null);
                refinedRows.add(PatternUtils.subst(refinedRow, subst3));
              }
            }
          }
          break;
        }
        if (covering == null) {
          j++;
        }
      }
    }

    // Report clauses that were not used
    for (int i = 0; i < actualClauses.size(); i++) {
      if (!actualUsages.containsKey(i)) {
        errorReporter.report(new RedundantClauseError(actualClauses.get(i)));
      }
    }

    // Find all actual rows with absurd patterns
    Set<Integer> absurdActualRows = new HashSet<>();
    for (int i = 0; i < actualRows.size(); i++) {
      if (PatternUtils.isAbsurd(actualRows.get(i))) {
        absurdActualRows.add(i);
      }
    }

    // For every refined row, we add a concrete clause to the resulting list of clauses
    List<ConcreteLetClause> letClauses = new ArrayList<>();
    List<ConcreteClause> resultClauses = new ArrayList<>();
    Map<Integer, ArendRef> letRefs = new HashMap<>();
    for (int i = 0; i < refinedRows.size(); i++) {
      Pair<Integer, Map<CoreBinding, CorePattern>> pair = refinedToActual.get(i);
      boolean isAbsurd = absurdActualRows.contains(pair.proj1);
      if (!isAbsurd) {
        for (CorePattern pattern : pair.proj2.values()) {
          if (PatternUtils.isAbsurd(pattern)) {
            isAbsurd = true;
            break;
          }
        }
      }

      if (!isAbsurd && (!pair.proj2.isEmpty() || actualUsages.get(pair.proj1) > 1)) {
        CoreParameter lamParams = PatternUtils.getAllBindings(actualRows.get(pair.proj1));
        boolean makeLet = actualUsages.get(pair.proj1) > 1;
        ArendRef letRef = makeLet ? letRefs.get(pair.proj1) : null;
        ConcreteExpression cExpr = null;
        if (!makeLet || letRef == null) {
          cExpr = pair.proj1 < actualClauses.size() ? actualClauses.get(pair.proj1).getExpression() : args.get(caseParam + 1).getExpression();
          if (cExpr == null) {
            errorReporter.report(new TypecheckingError("Clause must have a right hand side", actualClauses.get(pair.proj1)));
            return null;
          }
          if (lamParams != null) {
            List<ConcreteParameter> cParams = new ArrayList<>();
            Map<CoreBinding, ArendRef> bindings = new HashMap<>();
            for (CoreParameter param = lamParams; param.hasNext(); param = param.getNext()) {
              ArendRef lamRef = factory.local(ext.renamerFactory.getNameFromBinding(param.getBinding(), null));
              cParams.add(factory.param(lamRef));
              bindings.put(param.getBinding(), lamRef);
            }
            TypedExpression lamExpr = typechecker.typecheckLambda(factory.lam(cParams, factory.typed(cExpr, factory.meta("c" + (resultClauses.size() + 1) + "_type", new MetaDefinition() {
              @Override
              public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
                List<ConcreteExpression> args = new ArrayList<>();
                int l = 0;
                for (int j = 0; j < bodies.size(); j++) {
                  CoreExpression arg = PatternUtils.eval(bodies.get(j), actualRows.get(pair.proj1).subList(l, l + bodySizes.get(j)), typechecker, ext.renamerFactory, factory, bindings);
                  if (arg == null) {
                    return null;
                  }
                  args.add(factory.core(arg.computeTyped()));
                  l += bodySizes.get(j);
                }
                return typechecker.typecheck(factory.app(factory.core(resultLambda), true, args), null);
              }
            }))), lamParams);
            if (lamExpr == null) {
              return null;
            }
            cExpr = factory.core(lamExpr);
          }

          if (makeLet) {
            String name = "h" + (letClauses.size() + 1);
            letRef = factory.local(name);
            letRefs.put(pair.proj1, letRef);
            letClauses.add(factory.letClause(letRef, Collections.emptyList(), null, cExpr));
          }
        }

        Map<CoreBinding, ArendRef> bindings = new HashMap<>();
        List<ConcretePattern> cPatterns = PatternUtils.toConcrete(refinedRows.get(i), ext.renamerFactory, factory, bindings);
        CoreParameter param = PatternUtils.getAllBindings(actualRows.get(pair.proj1));
        ConcreteExpression rhs = makeLet ? factory.ref(letRef) : cExpr;
        if (param != null) {
          List<ConcreteExpression> rhsArgs = new ArrayList<>();
          for (; param.hasNext(); param = param.getNext()) {
            CorePattern pattern = pair.proj2.get(param.getBinding());
            rhsArgs.add(pattern == null ? factory.ref(param.getBinding()) : PatternUtils.toExpression(pattern, ext.renamerFactory, factory, bindings));
          }
          rhs = factory.app(rhs, true, rhsArgs);
        }
        resultClauses.add(factory.clause(cPatterns, rhs));
      } else {
        resultClauses.add(pair.proj1 < actualClauses.size() ? actualClauses.get(pair.proj1) : factory.clause(PatternUtils.toConcrete(actualRows.get(pair.proj1), ext.renamerFactory, factory, null), isAbsurd ? null : args.get(caseParam + 1).getExpression()));
      }
    }

    List<ConcreteCaseArgument> caseArgs = new ArrayList<>();
    List<ConcreteExpression> caseRefExprs = new ArrayList<>(subexpressionArgs.size());
    for (int i = 0; i < subexpressions.size(); i++) {
      int s = subexpressionArgs.get(i).size();
      List<ArendRef> refs = new ArrayList<>(s);
      List<CoreExpression> exprs = new ArrayList<>(s);
      List<ConcreteExpression> refExprs = new ArrayList<>(s);
      String name = "case_return_arg_" + (i + 1);
      for (int j = 0; j < s; j++) {
        TypedExpression typed = subexpressionArgs.get(i).get(j);
        ArendRef ref = factory.local(ext.renamerFactory.getNameFromType(typed.getType(), null));
        AbstractedExpression abstracted = bodyParameters.get(i).abstractType(j);
        List<ConcreteExpression> refExprsCopy = new ArrayList<>(refExprs);
        caseArgs.add(factory.caseArg(factory.core(typed), ref, factory.meta(name + "_" + (j + 1), new MetaDefinition() {
            @Override
            public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
              AbstractedExpression argType = typechecker.substituteAbstractedExpression(abstracted, refExprsCopy);
              return argType == null ? null : ((CoreExpression) argType).computeTyped();
            }
          })
        ));
        exprs.add(typed.getExpression());
        refs.add(ref);
        refExprs.add(factory.ref(ref));
      }
      caseRefExprs.add(factory.meta(name, new ReplaceSubexpressionsMeta(subexpressions.get(i), exprs, refs)));
    }

    ConcreteExpression result = factory.caseExpr(isSCase[0], caseArgs, factory.app(factory.core(resultLambda), true, caseRefExprs), null, resultClauses);
    return typechecker.typecheck(letClauses.isEmpty() ? result : factory.letExpr(false, letClauses, result), contextData.getExpectedType());
  }

  private static class ReplaceSubexpressionsMeta implements MetaDefinition {
    private final CoreExpression type;
    private final List<CoreExpression> subexpressions;
    private final List<ArendRef> subexpressionRefs;
    private int subexprIndex = 0;

    private ReplaceSubexpressionsMeta(CoreExpression type, List<CoreExpression> subexpressions, List<ArendRef> subexpressionRefs) {
      this.type = type;
      this.subexpressions = subexpressions;
      this.subexpressionRefs = subexpressionRefs;
    }

    @Override
    public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
      UncheckedExpression result = type.replaceSubexpressions(expr -> {
        if (subexprIndex < subexpressions.size() && subexpressions.get(subexprIndex) == expr) {
          CoreBinding binding = typechecker.getFreeBinding(subexpressionRefs.get(subexprIndex++));
          return binding == null ? null : binding.makeReference();
        }
        return null;
      });
      if (result == null) {
        typechecker.getErrorReporter().report(new TypecheckingError("Cannot substitute expressions", contextData.getMarker()));
        return null;
      }
      return typechecker.check(result, contextData.getMarker());
    }
  }

  // Each block correspond to a single function or \case expression.
  // It is a list of rows and each row is a sequence of patterns.
  // Each row has the same length.
  private <T> List<List<T>> product(List<? extends List<? extends List<? extends T>>> blocks) {
    List<List<T>> result = Collections.singletonList(Collections.emptyList());
    for (List<? extends List<? extends T>> block : blocks) {
      List<List<T>> newResult = new ArrayList<>();
      for (List<T> list : result) {
        for (List<? extends T> row : block) {
          List<T> newList = new ArrayList<>(list.size() + 1);
          newList.addAll(list);
          newList.addAll(row);
          newResult.add(newList);
        }
      }
      result = newResult;
    }

    return result;
  }
}
