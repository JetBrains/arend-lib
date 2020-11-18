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
import org.arend.ext.core.level.CoreSort;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.*;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Pair;
import org.arend.lib.pattern.PatternUtils;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;
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

  private static class SubexpressionData {
    final CoreElimBody body;
    final CoreSort sort; // the sort argument of the defCall
    final CoreExpression expression; // an occurrence of \case expressions or defCalls
    final List<? extends CoreExpression> originalArgs; // arguments of @expression
    final List<TypedExpression> matchedArgs; // arguments of @expression which will be actually matched
    final List<TypedExpression> removedArgs; // arguments of @expression with arguments that belong to matchedArgs replaced with null
    final Map<Integer, Integer> argsReindexing; // if argsReindexing.get(i) != null, then it is the index (in the list of all arguments of all \case expressions and defCalls) of an argument equivalent to the i-th argument of @expression

    private SubexpressionData(CoreElimBody body, CoreSort sort, CoreExpression expression, List<? extends CoreExpression> originalArgs, List<TypedExpression> matchedArgs, List<TypedExpression> removedArgs, Map<Integer, Integer> argsReindexing) {
      this.body = body;
      this.sort = sort;
      this.expression = expression;
      this.originalArgs = originalArgs;
      this.matchedArgs = matchedArgs;
      this.removedArgs = removedArgs;
      this.argsReindexing = argsReindexing;
    }
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteExpression marker = contextData.getMarker();
    ConcreteFactory factory = ext.factory.withData(marker);
    CoreExpression expectedType = contextData.getExpectedType().normalize(NormalizationMode.RNF);
    boolean[] isSCase = new boolean[] { false };

    // All of the following lists have the same length
    List<SubexpressionData> dataList = new ArrayList<>();
    List<CoreParameter> bodyParameters = new ArrayList<>(); // bodyParameters[i] is the parameters of dataList[i].body
    List<List<List<CorePattern>>> requiredBlocks = new ArrayList<>();
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
    Values<CoreExpression> values = new Values<>(typechecker, marker);
    expectedType.processSubexpression(expr -> {
      List<? extends CoreExpression> matchArgs = null;
      CoreElimBody body = null;
      CoreSort sort = null;
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
              sort = ((CoreFunCallExpression) expr).getSortArgument();
              parameters = def.getParameters();
            }
          }
          if (occurrences != null) {
            defCount.put(def, count + 1);
          }
        }
      }

      if (matchArgs != null) {
        Set<CoreBinding> matched = new HashSet<>();
        if (!body.getClauses().isEmpty()) {
          int i = 0;
          for (CoreParameter param = parameters; param.hasNext(); param = param.getNext(), i++) {
            for (CoreElimClause clause : body.getClauses()) {
              if (clause.getPatterns().get(i).getBinding() == null) {
                matched.add(param.getBinding());
                CoreFunCallExpression funCall = param.getTypeExpr().toEquality(); // try to take the type immediately
                if (funCall == null) { // if it's not an equality, then this may be because we need to substitute patterns
                  CoreExpression type = (CoreExpression) typechecker.substituteAbstractedExpression(parameters.abstractType(i), sort, PatternUtils.toExpression(clause.getPatterns().subList(0, i), ext, factory, null));
                  funCall = type == null ? null : type.toEquality();
                  if (funCall != null) {
                    List<CoreBinding> patternBindings = new ArrayList<>(2);
                    if (funCall.getDefCallArguments().get(1) instanceof CoreReferenceExpression) {
                      patternBindings.add(((CoreReferenceExpression) funCall.getDefCallArguments().get(1)).getBinding());
                    }
                    if (funCall.getDefCallArguments().get(2) instanceof CoreReferenceExpression) {
                      patternBindings.add(((CoreReferenceExpression) funCall.getDefCallArguments().get(2)).getBinding());
                    }
                    if (!patternBindings.isEmpty()) {
                      CoreParameter param1 = parameters;
                      for (CorePattern pattern : clause.getPatterns()) {
                        if (pattern.getBinding() != null && patternBindings.contains(pattern.getBinding())) {
                          matched.add(param1.getBinding());
                        }
                        param1 = param1.getNext();
                      }
                    }
                  }
                } else {
                  if (funCall.getDefCallArguments().get(1) instanceof CoreReferenceExpression) {
                    matched.add(((CoreReferenceExpression) funCall.getDefCallArguments().get(1)).getBinding());
                  }
                  if (funCall.getDefCallArguments().get(2) instanceof CoreReferenceExpression) {
                    matched.add(((CoreReferenceExpression) funCall.getDefCallArguments().get(2)).getBinding());
                  }
                }
                break;
              }
            }
          }
        }
        if (parameters.hasNext()) {
          for (CoreParameter param = parameters.getNext(); param.hasNext(); param = param.getNext()) {
            if (param.getTypeExpr().findFreeBindings(matched) != null) {
              matched.add(param.getBinding());
            }
          }
        }

        List<TypedExpression> matchedArgs = new ArrayList<>();
        List<TypedExpression> removedArgs = new ArrayList<>(matchArgs.size());
        Map<Integer, Integer> argsReindexing = new HashMap<>();
        List<ConcreteExpression> removedConcrete = new ArrayList<>(matchArgs.size());
        CoreParameter param = parameters;
        for (int i = 0; i < matchArgs.size(); i++) {
          CoreExpression argument = matchArgs.get(i);
          if (matched.contains(param.getBinding())) {
            int size = values.getValues().size();
            int index = values.addValue(argument);
            if (index == size) {
              matchedArgs.add(argument.computeTyped());
              removedConcrete.add(null);
            } else {
              argsReindexing.put(i, index);
              removedConcrete.add(factory.ref(findParameter(bodyParameters, index).getBinding()));
            }
            removedArgs.add(null);
          } else {
            TypedExpression typed = argument.computeTyped();
            removedArgs.add(typed);
            removedConcrete.add(factory.core(typed));
          }
          param = param.getNext();
        }

        CoreParameter reducedParameters = typechecker.substituteParameters(parameters, sort, removedConcrete);
        if (reducedParameters == null) {
          return CoreExpression.FindAction.CONTINUE;
        }

        dataList.add(new SubexpressionData(body, sort, expr, matchArgs, matchedArgs, removedArgs, argsReindexing));
        bodyParameters.add(reducedParameters);

        List<List<CorePattern>> block = new ArrayList<>();
        for (CoreElimClause clause : body.getClauses()) {
          List<CorePattern> row = removeColumnsInRow(clause.getPatterns(), removedArgs);
          CoreParameter patternsParams = PatternUtils.getAllBindings(clause.getPatterns());
          if (patternsParams != null) {
            List<ConcreteExpression> substExprs = new ArrayList<>();
            for (int i = 0; i < removedArgs.size(); i++) {
              if (removedArgs.get(i) != null) {
                substExprs.add(factory.core(removedArgs.get(i)));
              } else {
                int s = PatternUtils.getNumberOfBindings(clause.getPatterns().get(i));
                for (int j = 0; j < s; j++) {
                  substExprs.add(null);
                }
              }
            }
            row = PatternUtils.replaceParameters(row, typechecker.substituteParameters(patternsParams, sort, substExprs), ext.renamerFactory);
          }
          block.add(row);
        }

        requiredBlocks.add(block);
        refinedBlocks.add(removeColumnsInRows(body.computeRefinedPatterns(parameters), removedArgs));
        return caseOccurrences != null && caseOccurrences.isEmpty() && defCount.isEmpty() ? CoreExpression.FindAction.STOP : CoreExpression.FindAction.CONTINUE;
      }

      return CoreExpression.FindAction.CONTINUE;
    });

    CoreParameter caseParams = typechecker.mergeParameters(bodyParameters);
    if (!caseParams.hasNext()) {
      errorReporter.report(new TypecheckingError("Cannot find matching subexpressions", marker));
      return null;
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
    TypedExpression resultLambda;
    Set<Pair<Integer, Integer>> abstractedArgs;
    {
      List<CoreExpression> expressionsToAbstract = new ArrayList<>();
      List<Pair<Integer, Integer>> indicesToAbstract = new ArrayList<>(); // pair (i,-1) refers to dataList[i].expression and pair (i,j) refers to dataList[i],matchedArgs[j]
      Map<Pair<Integer, Integer>, ArendRef> argRefs = new HashMap<>();
      typechecker.withCurrentState(tc -> {
        expectedType.processSubexpression(expr -> {
          CoreExpression exprType = expr.computeType();
          if (exprType.isError()) return CoreExpression.FindAction.CONTINUE;

          for (int i = 0; i < dataList.size(); i++) {
            if (expr == dataList.get(i).expression) {
              indicesToAbstract.add(new Pair<>(i, -1));
              expressionsToAbstract.add(expr);
              return CoreExpression.FindAction.SKIP;
            }
          }
          for (int i = 0; i < dataList.size(); i++) {
            List<TypedExpression> matchedArgs = dataList.get(i).matchedArgs;
            for (int j = 0; j < matchedArgs.size(); j++) {
              TypedExpression arg = matchedArgs.get(j);
              if (tc.compare(arg.getType(), exprType, CMP.EQ, marker, false, true) && tc.compare(arg.getExpression(), expr, CMP.EQ, marker, false, true)) {
                tc.updateSavedState();
                var pair = new Pair<>(i, j);
                indicesToAbstract.add(pair);
                expressionsToAbstract.add(expr);
                argRefs.computeIfAbsent(pair, k -> factory.local(ext.renamerFactory.getNameFromType(arg.getType(), null)));
              } else {
                tc.loadSavedState();
              }
            }
          }
          return CoreExpression.FindAction.CONTINUE;
        });
        return null;
      });

      List<CoreExpression> lambdaTypes = new ArrayList<>();
      List<ConcreteParameter> lambdaParams = new ArrayList<>();
      for (int i = 0; i < dataList.size(); i++) {
        SubexpressionData data = dataList.get(i);
        for (int j = 0; j < data.matchedArgs.size(); j++) {
          ArendRef ref = argRefs.get(new Pair<>(i, j));
          if (ref != null) {
            lambdaParams.add(factory.param(ref));
            lambdaTypes.add(data.matchedArgs.get(j).getType());
          }
        }

        CoreExpression type = data.expression.computeType();
        ArendRef ref = factory.local(ext.renamerFactory.getNameFromType(type, null));
        lambdaParams.add(factory.param(ref));
        lambdaTypes.add(type);
        argRefs.put(new Pair<>(i, -1), ref);
      }

      List<ArendRef> replacementRefs = new ArrayList<>(indicesToAbstract.size());
      for (Pair<Integer, Integer> pair : indicesToAbstract) {
        replacementRefs.add(argRefs.get(pair));
      }

      resultLambda = typechecker.typecheckLambda((ConcreteLamExpression) factory.lam(lambdaParams, factory.meta("case_return_lambda", new ReplaceSubexpressionsMeta(expectedType, expressionsToAbstract, replacementRefs))), typechecker.makeParameters(lambdaTypes, marker));
      if (resultLambda == null) {
        return null;
      }
      abstractedArgs = argRefs.keySet();
    }

    List<List<CorePattern>> requiredBlock = removeRedundantRows(mergeColumns(product(requiredBlocks), dataList));
    List<List<CorePattern>> refinedBlock = mergeColumns(product(refinedBlocks), dataList);

    // Find coverings of required rows by actual rows
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

    // For every refined row, add a concrete clause to the resulting list of clauses
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

      List<CorePattern> actualRow = actualRows.get(pair.proj1);
      if (!isAbsurd && (!pair.proj2.isEmpty() || actualUsages.get(pair.proj1) > 1)) {
        CoreParameter lamParams = PatternUtils.getAllBindings(actualRow);
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
            TypedExpression lamExpr = typechecker.typecheckLambda((ConcreteLamExpression) factory.lam(cParams, factory.typed(cExpr, factory.meta("c" + (resultClauses.size() + 1) + "_type", new MetaDefinition() {
              @Override
              public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
                List<ConcreteExpression> args = new ArrayList<>();
                int l = 0;
                for (int j = 0; j < dataList.size(); j++) {
                  SubexpressionData data = dataList.get(j);
                  for (int k = 0; k < data.matchedArgs.size(); k++) {
                    if (abstractedArgs.contains(new Pair<>(j, k))) {
                      args.add(PatternUtils.toExpression(actualRow.get(l + k), ext, factory, bindings));
                    }
                  }

                  List<CorePattern> patternArgs = new ArrayList<>();
                  for (int k = 0; k < data.removedArgs.size(); k++) {
                    if (data.removedArgs.get(k) == null) {
                      Integer index = data.argsReindexing.get(k);
                      patternArgs.add(actualRow.get(index == null ? l++ : index));
                    } else {
                      patternArgs.add(null);
                    }
                  }
                  CoreExpression arg = PatternUtils.eval(data.body, data.sort, patternArgs, data.removedArgs, typechecker, ext, factory, bindings);
                  if (arg == null) {
                    return null;
                  }
                  args.add(factory.core(arg.computeTyped()));
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
        CoreParameter param = PatternUtils.getAllBindings(actualRow);
        ConcreteExpression rhs = makeLet ? factory.ref(letRef) : cExpr;
        if (param != null) {
          List<ConcreteExpression> rhsArgs = new ArrayList<>();
          for (; param.hasNext(); param = param.getNext()) {
            CorePattern pattern = pair.proj2.get(param.getBinding());
            rhsArgs.add(pattern == null ? factory.ref(param.getBinding()) : PatternUtils.toExpression(pattern, ext, factory, bindings));
          }
          rhs = factory.app(rhs, true, rhsArgs);
        }
        resultClauses.add(factory.clause(cPatterns, rhs));
      } else {
        resultClauses.add(pair.proj1 < actualClauses.size() ? actualClauses.get(pair.proj1) : factory.clause(PatternUtils.toConcrete(actualRow, ext.renamerFactory, factory, null), isAbsurd ? null : args.get(caseParam + 1).getExpression()));
      }
    }

    // Construct arguments for the resulting \case expression
    List<ConcreteCaseArgument> caseArgs = new ArrayList<>();
    List<ConcreteExpression> caseRefExprs = new ArrayList<>(dataList.size());
    List<List<ArendRef>> refLists = new ArrayList<>();
    for (int i = 0; i < dataList.size(); i++) {
      SubexpressionData data = dataList.get(i);
      List<ArendRef> refs = new ArrayList<>();
      List<ArendRef> refList = new ArrayList<>();
      List<CoreExpression> exprs = new ArrayList<>();
      List<ConcreteExpression> refExprs = new ArrayList<>();
      String name = "case_return_arg_" + (i + 1);
      for (int j = 0, k = 0; j < data.removedArgs.size(); j++) {
        if (data.removedArgs.get(j) != null) {
          continue;
        }

        Integer index = data.argsReindexing.get(j);
        Pair<Integer, Integer> pair = index == null ? new Pair<>(i, k++) : findArgument(dataList, index);

        if (index == null) {
          TypedExpression typed = dataList.get(pair.proj1).matchedArgs.get(pair.proj2);
          ArendRef ref = factory.local(ext.renamerFactory.getNameFromType(typed.getType(), null));
          ConcreteExpression refExpr = factory.ref(ref);
          if (abstractedArgs.contains(pair)) {
            caseRefExprs.add(refExpr);
          }
          AbstractedExpression abstracted = bodyParameters.get(pair.proj1).abstractType(refExprs.size());
          List<ConcreteExpression> refExprsCopy = new ArrayList<>(refExprs);
          CoreSort sort = dataList.get(pair.proj1).sort;
          caseArgs.add(factory.caseArg(factory.core(typed), ref, factory.meta(name + "_" + (j + 1), new MetaDefinition() {
              @Override
              public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
                AbstractedExpression argType = typechecker.substituteAbstractedExpression(abstracted, sort, refExprsCopy);
                return argType == null ? null : ((CoreExpression) argType).computeTyped();
              }
            })
          ));
          exprs.add(typed.getExpression());
          refs.add(ref);
          refList.add(ref);
          refExprs.add(refExpr);
        } else {
          exprs.add(data.originalArgs.get(j));
          refs.add(refLists.get(pair.proj1).get(pair.proj2));
        }
      }

      refLists.add(refList);
      caseRefExprs.add(factory.meta(name, new ReplaceSubexpressionsMeta(data.expression, exprs, refs)));
    }

    // Typecheck the result
    ConcreteExpression result = factory.caseExpr(isSCase[0], caseArgs, factory.app(factory.core(resultLambda), true, caseRefExprs), null, resultClauses);
    return typechecker.typecheck(letClauses.isEmpty() ? result : factory.letExpr(false, letClauses, result), contextData.getExpectedType());
  }

  private static class ReplaceSubexpressionsMeta implements MetaDefinition {
    private final CoreExpression type;
    private final List<CoreExpression> subexpressions;
    private final List<ArendRef> subexpressionRefs;
    private int subexprIndex;

    private ReplaceSubexpressionsMeta(CoreExpression type, List<CoreExpression> subexpressions, List<ArendRef> subexpressionRefs) {
      this.type = type;
      this.subexpressions = subexpressions;
      this.subexpressionRefs = subexpressionRefs;
    }

    @Override
    public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
      subexprIndex = 0;
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
  private static <T> List<List<T>> product(List<? extends List<? extends List<? extends T>>> blocks) {
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

  private static <T,S> List<T> removeColumnsInRow(List<? extends T> row, List<S> removedArgs) {
    List<T> newRow = new ArrayList<>();
    for (int j = 0; j < row.size(); j++) {
      if (removedArgs.get(j) == null) {
        newRow.add(row.get(j));
      }
    }
    return newRow;
  }

  private static <T,S> List<List<T>> removeColumnsInRows(List<? extends List<? extends T>> rows, List<S> removedArgs) {
    List<List<T>> newRows = new ArrayList<>(rows.size());
    for (List<? extends T> row : rows) {
      newRows.add(removeColumnsInRow(row, removedArgs));
    }
    return newRows;
  }

  private static CoreParameter findParameter(List<CoreParameter> parameters, int index) {
    int i = 0;
    for (CoreParameter param : parameters) {
      for (; param.hasNext(); param = param.getNext(), i++) {
        if (i == index) {
          return param;
        }
      }
    }
    throw new IllegalStateException();
  }

  private static Pair<Integer, Integer> findArgument(List<SubexpressionData> dataList, int index) {
    int k = 0;
    for (int i = 0; i < dataList.size(); i++) {
      SubexpressionData data = dataList.get(i);
      if (index < k + data.matchedArgs.size()) {
        return new Pair<>(i, index - k);
      }
      k += data.matchedArgs.size();
    }
    throw new IllegalStateException();
  }

  private static List<List<CorePattern>> mergeColumns(List<List<CorePattern>> rows, List<SubexpressionData> dataList) {
    int j = 0;
    for (SubexpressionData data : dataList) {
      if (data.argsReindexing.isEmpty()) {
        j += data.removedArgs.size();
        continue;
      }

      for (int k = 0; k < data.removedArgs.size(); k++, j++) {
        Integer i = data.argsReindexing.get(k);
        if (i == null) continue;
        List<List<CorePattern>> newRows = new ArrayList<>();
        for (List<CorePattern> row : rows) {
          Map<CoreBinding, CorePattern> subst1 = new HashMap<>();
          Map<CoreBinding, CorePattern> subst2 = new HashMap<>();
          if (PatternUtils.unify(row.get(i), row.get(j), subst1, subst2)) {
            List<CorePattern> newRow = new ArrayList<>(row.size() - 1);
            newRow.addAll(row.subList(0, i));
            newRow.add(row.get(i).subst(subst1));
            newRow.addAll(row.subList(i + 1, j));
            newRow.addAll(row.subList(j + 1, row.size()));
            newRows.add(newRow);
          }
        }
        rows = newRows;
      }
    }
    return rows;
  }

  private static List<List<CorePattern>> removeRedundantRows(List<List<CorePattern>> rows) {
    List<List<CorePattern>> newRows = new ArrayList<>();
    loop:
    for (int i = 0; i < rows.size(); i++) {
      for (int j = 0; j < i; j++) {
        if (PatternUtils.refines(rows.get(i), rows.get(j))) {
          continue loop;
        }
      }
      newRows.add(rows.get(i));
    }
    return newRows;
  }
}