package org.arend.lib.meta;

import org.arend.ext.concrete.*;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.core.body.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.context.CoreParameterBuilder;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.level.LevelSubstitution;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.error.*;
import org.arend.ext.error.quickFix.RemoveErrorQuickFix;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.error.IgnoredArgumentError;
import org.arend.lib.error.TypeError;
import org.arend.lib.meta.util.ReplaceSubexpressionsMeta;
import org.arend.lib.meta.util.SubstitutionMeta;
import org.arend.lib.pattern.ArendPattern;
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
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    if (!new ContextDataChecker() {
      @Override
      public boolean @Nullable [] argumentExplicitness() {
        return new boolean[] { false, false, true, true };
      }

      @Override
      public int numberOfOptionalExplicitArguments() {
        return 2;
      }

      @Override
      public boolean allowClauses() {
        return true;
      }
    }.checkContextData(contextData, resolver.getErrorReporter())) {
      return null;
    }

    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    List<? extends ConcreteArgument> args = contextData.getArguments();

    int paramsIndex = -1;
    if (!args.isEmpty() && !args.get(0).isExplicit()) {
      if (args.size() >= 2 && !args.get(1).isExplicit()) {
        paramsIndex = 1;
      } else {
        if (args.get(0).getExpression() instanceof ConcreteAppExpression) {
          paramsIndex = 0;
        } else if (args.get(0).getExpression() instanceof ConcreteTupleExpression tupleExpr) {
          if (!tupleExpr.getFields().isEmpty() && tupleExpr.getFields().get(0) instanceof ConcreteAppExpression) {
            paramsIndex = 0;
          }
        }
      }
    }
    boolean hasDefinitionArg = !args.isEmpty() && !args.get(0).isExplicit() && paramsIndex != 0;
    int caseArgsIndex = -1;
    int defaultIndex = -1;
    int firstExplicitIndex = paramsIndex >= 0 ? paramsIndex + 1 : hasDefinitionArg ? 1 : 0;
    if (firstExplicitIndex + 1 < args.size()) {
      caseArgsIndex = firstExplicitIndex;
      if (!(args.get(firstExplicitIndex + 1).getExpression() instanceof ConcreteHoleExpression)) {
        defaultIndex = firstExplicitIndex + 1;
      }
    } else if (firstExplicitIndex < args.size()) {
      defaultIndex = firstExplicitIndex;
    }

    ConcreteAppBuilder builder = factory.appBuilder(contextData.getReferenceExpression());
    if (hasDefinitionArg) {
      builder.app(resolver.resolve(args.get(0).getExpression()), false);
    } else if (paramsIndex != -1) {
      builder.app(factory.hole(), false);
    }
    if (paramsIndex != -1) {
      List<ConcreteExpression> fields = new ArrayList<>();
      List<? extends ConcreteExpression> params = Utils.getArgumentList(args.get(paramsIndex).getExpression());
      for (ConcreteExpression param : params) {
        List<ConcreteArgument> seq = param.getArgumentsSequence();
        if (seq.size() == 2 && seq.get(0).getExpression() instanceof ConcreteReferenceExpression && seq.get(1).isExplicit() && ((ConcreteReferenceExpression) seq.get(0).getExpression()).getReferent().getRefName().equals(ext.casesMeta.argRef.getRefName())) {
          ConcreteExpression field = ext.casesMeta.parameter.resolve(resolver, seq.get(1).getExpression(), false, true);
          if (field != null) fields.add(field);
        } else {
          resolver.getErrorReporter().report(new NameResolverError("Expected 'arg' with one explicit argument", param));
        }
      }
      builder.app(factory.tuple(fields), false);
    }

    ConcreteExpression caseArgs = caseArgsIndex == -1 ? factory.tuple() : ext.casesMeta.resolveArgument(resolver, args.get(caseArgsIndex).getExpression());
    builder.app(caseArgs);
    builder.app(resolver.resolve(factory.caseExpr(false, Collections.emptyList(), null, null, contextData.getClauses() == null ? Collections.emptyList() : contextData.getClauses().getClauseList())));
    if (defaultIndex != -1) {
      builder.app(ext.casesMeta.resolveDefaultClause(resolver, args.get(defaultIndex).getExpression(), caseArgs));
    } else {
      ext.casesMeta.resolveDefaultClause(resolver, null, caseArgs);
    }
    return builder.build();
  }

  @Override
  public int @Nullable [] desugarArguments(@NotNull List<? extends ConcreteArgument> arguments) {
    if (arguments.isEmpty() || arguments.get(0).isExplicit()) return null;
    if (arguments.size() == 1) return new int[0];
    int first = arguments.get(1).isExplicit() ? 1 : 2;
    int[] result = new int[arguments.size() - first];
    for (int i = 0; i < result.length; i++) {
      result[i] = i + first;
    }
    return result;
  }

  /**
   * @param levelSubst     the level arguments of the defCall
   * @param expression     an occurrence of \case expressions or defCalls
   * @param matchedArgs    arguments of @expression which will be actually matched
   * @param removedArgs    arguments of @expression with arguments that belong to matchedArgs replaced with null
   * @param argsReindexing if argsReindexing.get(i) != null, then it is the index (in the list of all arguments of all \case expressions and defCalls) of an argument equivalent to the i-th argument of @expression
   */
  private record SubexpressionData(CoreElimBody body, LevelSubstitution levelSubst, CoreExpression expression,
                                   List<TypedExpression> matchedArgs, List<TypedExpression> removedArgs,
                                   Map<Integer, Integer> argsReindexing) {

    List<? extends CoreExpression> getOriginalArgs() {
        if (expression instanceof CoreFunCallExpression) {
          return ((CoreFunCallExpression) expression).getDefCallArguments();
        } else if (expression instanceof CoreCaseExpression) {
          return ((CoreCaseExpression) expression).getArguments();
        } else {
          throw new IllegalStateException();
        }
      }
    }

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    // arguments: definitions specification (implicit), parameters of matched expressions (implicit), additional expressions to match (explicit), the case expression with clauses (explicit), the default expression (optional)
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

    // Parse definitions specification
    Set<Integer> caseOccurrences; // we are looking for \case expressions if caseOccurrences is either null or non-empty
    Map<CoreFunctionDefinition, Integer> defCount = new HashMap<>(); // if defCount.get(def) != null, then we are looking for def
    Map<CoreFunctionDefinition, Set<Integer>> defOccurrences = new HashMap<>(); // if we are looking for def and defOccurrences.get(def) == null, then we are looking for all occurrences; otherwise only for the specified ones; defOccurrences.get(def) is never empty
    if (!args.get(0).isExplicit() && !(args.get(0).getExpression() instanceof ConcreteHoleExpression)) {
      List<? extends ConcreteExpression> params = Utils.getArgumentList(args.get(0).getExpression());
      if (params.isEmpty()) {
        errorReporter.report(new IgnoredArgumentError(args.get(0).getExpression()));
        caseOccurrences = null;
      } else {
        List<Pair<ConcreteExpression, List<? extends ConcreteExpression>>> lists = new ArrayList<>();
        List<ConcreteExpression> defList = new ArrayList<>();
        for (ConcreteExpression param : params) {
          if (param instanceof ConcreteTupleExpression) {
            lists.add(new Pair<>(param, Utils.getArgumentList(param)));
          } else {
            defList.add(param);
          }
        }
        if (!defList.isEmpty()) {
          lists.add(new Pair<>(null, defList));
        }

        Set<Integer> myCaseOccurrences = new HashSet<>();
        for (Pair<ConcreteExpression, List<? extends ConcreteExpression>> pair : lists) {
          Set<Integer> occurrences = new HashSet<>();
          for (ConcreteExpression param : pair.proj2) {
            if (param instanceof ConcreteNumberExpression) {
              occurrences.add(((ConcreteNumberExpression) param).getNumber().intValue());
            } else if (!(param instanceof ConcreteReferenceExpression)) {
              errorReporter.report(new TypecheckingError("Unrecognized parameter", param));
            }
          }
          boolean isCase = true;
          for (ConcreteExpression param : pair.proj2) {
            if (param instanceof ConcreteReferenceExpression) {
              CoreDefinition def = ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) param).getReferent());
              if (def instanceof CoreFunctionDefinition && ((CoreFunctionDefinition) def).getBody() instanceof CoreElimBody) {
                isCase = false;
                if (defCount.putIfAbsent((CoreFunctionDefinition) def, 0) == null) {
                  if (!occurrences.isEmpty()) {
                    defOccurrences.put((CoreFunctionDefinition) def, occurrences);
                  }
                } else {
                  TypecheckingError error = new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Parameters for '" + def.getName() + "' are already specified", pair.proj1 != null ? pair.proj1 : param);
                  errorReporter.report(pair.proj1 != null ? error.withQuickFix(new RemoveErrorQuickFix("Remove")) : error);
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
              errorReporter.report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Parameters for \\case expressions are already specified", pair.proj2.isEmpty() ? args.get(0).getExpression() : pair.proj2.get(0)));
            }
          }
        }
        caseOccurrences = myCaseOccurrences;
      }
    } else {
      caseOccurrences = null;
    }

    List<Boolean> addPathList = new ArrayList<>();
    if (!args.get(1).isExplicit()) {
      for (ConcreteExpression arg : Utils.getArgumentList(args.get(1).getExpression())) {
        addPathList.add(ext.casesMeta.parameter.containsKey(arg, ext.casesMeta.addPathRef));
      }
    }

    int additionalArgsIndex = args.get(0).isExplicit() ? 0 : args.get(1).isExplicit() ? 1 : 2;
    List<CasesMeta.ArgParameters> argParamsList = new ArrayList<>();
    List<Pair<TypedExpression,CoreExpression>> additionalArgs = new ArrayList<>();
    for (ConcreteExpression additionalArg : Utils.getArgumentList(args.get(additionalArgsIndex).getExpression())) {
      CasesMeta.ArgParameters argParams = ext.casesMeta.new ArgParameters(additionalArg, errorReporter, false);
      TypedExpression typed = typechecker.typecheck(argParams.expression, null);
      if (typed == null) return null;
      additionalArgs.add(new Pair<>(typed, typed.getType().normalize(NormalizationMode.RNF)));
      argParamsList.add(argParams);
    }

    // Find subexpressions
    List<CoreExpression> expressionsToProcess = new ArrayList<>(additionalArgs.size() + 1);
    for (var additionalArg : additionalArgs) {
      expressionsToProcess.add(additionalArg.proj2);
    }
    expressionsToProcess.add(expectedType);
    int[] caseCount = { 0 };
    Values<CoreExpression> values = new Values<>(typechecker, marker);
    List<List<SubexpressionData>> argsDataLists = new ArrayList<>();
    for (CoreExpression expression : expressionsToProcess) {
      int start = dataList.size();
      expression.processSubexpression(expr -> {
        List<? extends CoreExpression> matchArgs = null;
        CoreElimBody body = null;
        LevelSubstitution levelSubst = LevelSubstitution.EMPTY;
        CoreParameter parameters = null;
        if (expr instanceof CoreCaseExpression caseExpr && (caseOccurrences == null || caseOccurrences.remove(++caseCount[0]))) {
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
                if (def.getKind() == CoreFunctionDefinition.Kind.SFUNC || def.getKind() == CoreFunctionDefinition.Kind.TYPE) {
                  isSCase[0] = true;
                }
                matchArgs = ((CoreFunCallExpression) expr).getDefCallArguments();
                body = (CoreElimBody) body1;
                levelSubst = ((CoreFunCallExpression) expr).getLevels().makeSubstitution(def);
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
                    CoreExpression type = (CoreExpression) typechecker.substituteAbstractedExpression(parameters.abstractType(i), levelSubst, PatternUtils.toExpression(clause.getPatterns().subList(0, i), ext, factory, null), null);
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

          CoreParameter reducedParameters = typechecker.substituteParameters(parameters, levelSubst, removedConcrete);
          if (reducedParameters == null) {
            return CoreExpression.FindAction.CONTINUE;
          }

          dataList.add(new SubexpressionData(body, levelSubst, expr, matchedArgs, removedArgs, argsReindexing));
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
              row = PatternUtils.replaceParameters(row, typechecker.substituteParameters(patternsParams, levelSubst, substExprs), ext.renamerFactory);
            }
            block.add(row);
          }

          requiredBlocks.add(block);
          refinedBlocks.add(removeColumnsInRows(body.computeRefinedPatterns(parameters), removedArgs));
          return caseOccurrences != null && caseOccurrences.isEmpty() && defCount.isEmpty() ? CoreExpression.FindAction.STOP : CoreExpression.FindAction.CONTINUE;
        }

        return CoreExpression.FindAction.CONTINUE;
      });
      argsDataLists.add(dataList.subList(start, dataList.size()));
    }
    List<SubexpressionData> resultDataList = argsDataLists.remove(argsDataLists.size() - 1);

    int caseParam = additionalArgsIndex + 1;
    List<? extends ConcreteClause> actualClauses = ((ConcreteCaseExpression) args.get(caseParam).getExpression()).getClauses();
    ConcreteExpression defaultExpr = caseParam + 1 < args.size() ? args.get(caseParam + 1).getExpression() : null;

    int numberOfParameters = 0;
    for (CoreParameter param : bodyParameters) {
      numberOfParameters += Utils.parametersSize(param);
    }
    if (numberOfParameters == 0) {
      if (defaultExpr != null) {
        for (ConcreteClause clause : actualClauses) {
          errorReporter.report(new RedundantClauseError(clause));
        }
        return typechecker.typecheck(defaultExpr, expectedType);
      }
      errorReporter.report(new TypecheckingError("Cannot find matching subexpressions", marker));
      return null;
    }
    if (addPathList.size() > numberOfParameters) {
      errorReporter.report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Too many parameters", ((ConcreteTupleExpression) args.get(1).getExpression()).getFields().get(addPathList.size() - numberOfParameters)));
      addPathList.subList(numberOfParameters, addPathList.size()).clear();
    }
    if (!argParamsList.isEmpty()) {
      for (int i = addPathList.size(); i < numberOfParameters; i++) {
        addPathList.add(false);
      }
      for (CasesMeta.ArgParameters parameters : argParamsList) {
        addPathList.add(parameters.addPath);
      }
    }
    for (int i = addPathList.size() - 1; i >= 0; i--) {
      if (addPathList.get(i)) {
        break;
      }
      addPathList.remove(i);
    }

    CoreParameterBuilder parameterBuilder = typechecker.newCoreParameterBuilder();
    for (CoreParameter bodyParameter : bodyParameters) {
      parameterBuilder.addCopyLast(bodyParameter, true);
    }
    CoreParameter additionalParameters = null;
    if (!additionalArgs.isEmpty()) {
      List<Pair<TypedExpression,Object>> substPairs = new ArrayList<>();
      CoreParameter param = parameterBuilder.getFirst();
      for (SubexpressionData data : dataList) {
        for (TypedExpression matchedArg : data.matchedArgs) {
          substPairs.add(new Pair<>(matchedArg, param.getBinding()));
          param = param.getNext();
        }
      }
      for (var additionalArg : additionalArgs) {
        TypedExpression replaced = new ReplaceSubexpressionsMeta(additionalArg.proj2, substPairs).invoke(typechecker, marker);
        CoreParameter newParam = parameterBuilder.addLast(true, null, replaced == null ? additionalArg.proj2 : replaced.getExpression(), marker);
        if (additionalParameters == null) {
          additionalParameters = newParam;
        }
      }
    }
    CoreParameter caseParams = parameterBuilder.getFirst();

    // Insert paths from addPath
    if (!addPathList.isEmpty()) {
      List<TypedExpression> allMatchedArgs = new ArrayList<>();
      for (SubexpressionData data : dataList) {
        allMatchedArgs.addAll(data.matchedArgs);
      }
      for (var additionalArg : additionalArgs) {
        allMatchedArgs.add(additionalArg.proj1);
      }

      Map<CoreParameter, CoreParameter> addPathMap = new HashMap<>();
      CoreParameter param = caseParams;
      int i = 0;
      for (Boolean addPath : addPathList) {
        if (!param.hasNext()) break;
        if (addPath) {
          CoreParameter addPathParam = typechecker.typecheckParameters(Collections.singletonList(factory.param(true, factory.app(factory.ref(ext.prelude.getEqualityRef()), true, factory.core(allMatchedArgs.get(i)), factory.core(param.getBinding().makeReference().computeTyped())))));
          if (addPathParam == null) return null;
          addPathMap.put(param, addPathParam);
        }
        param = param.getNext();
        i++;
      }

      caseParams = caseParams.insertParameters(addPathMap);
    }

    List<List<CorePattern>> actualRows = new ArrayList<>();
    if (!actualClauses.isEmpty()) {
      boolean ok = true;
      int s = Utils.parametersSize(caseParams);
      for (ConcreteClause clause : actualClauses) {
        if (clause.getPatterns().size() != s) {
          errorReporter.report(new TypecheckingError("Expected " + s + " pattern" + (s == 1 ? "" : "s"), clause));
          ok = false;
          continue;
        }
        List<CoreExpressionPattern> row = typechecker.typecheckPatterns(clause.getPatterns(), caseParams, clause);
        if (row == null) {
          ok = false;
          continue;
        }
        actualRows.add(new ArrayList<>(row));
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

          for (int i = 0; i < resultDataList.size(); i++) {
            CoreExpression resultExpr = resultDataList.get(i).expression;
            boolean ok = expr == resultExpr;
            if (!ok) {
              if (tc.compare(resultExpr.computeType(), exprType, CMP.EQ, marker, false, true, false) && tc.compare(resultExpr, expr, CMP.EQ, marker, false, true, true)) {
                tc.updateSavedState();
                ok = true;
              } else {
                tc.loadSavedState();
              }
            }
            if (ok) {
              indicesToAbstract.add(new Pair<>(i + dataList.size() - resultDataList.size(), -1));
              expressionsToAbstract.add(expr);
              return CoreExpression.FindAction.SKIP;
            }
          }
          for (int i = 0; i < dataList.size(); i++) {
            List<TypedExpression> matchedArgs = dataList.get(i).matchedArgs;
            for (int j = 0; j < matchedArgs.size(); j++) {
              TypedExpression arg = matchedArgs.get(j);
              if (tc.compare(arg.getType(), exprType, CMP.EQ, marker, false, true, false) && tc.compare(arg.getExpression(), expr, CMP.EQ, marker, false, true, true)) {
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

      List<ConcreteParameter> lambdaTypesParams = new ArrayList<>();
      List<ConcreteParameter> lambdaParams = new ArrayList<>();
      for (int i = 0; i < dataList.size(); i++) {
        SubexpressionData data = dataList.get(i);
        for (int j = 0; j < data.matchedArgs.size(); j++) {
          ArendRef ref = argRefs.get(new Pair<>(i, j));
          if (ref != null) {
            lambdaParams.add(factory.param(ref));
            lambdaTypesParams.add(factory.param(Collections.singletonList(ref), factory.core(data.matchedArgs.get(j).getType().computeTyped())));
          }
        }
      }

      for (int i = 0; i < resultDataList.size(); i++) {
        SubexpressionData data = resultDataList.get(i);
        CoreExpression expr = data.expression;
        CoreExpression resultType;
        CoreParameter parameter;
        LevelSubstitution levelSubst;
        if (expr instanceof CoreFunCallExpression funCall) {
          parameter = funCall.getDefinition().getParameters();
          resultType = funCall.getDefinition().getResultType();
          levelSubst = funCall.getLevels().makeSubstitution(funCall.getDefinition());
        } else if (expr instanceof CoreCaseExpression) {
          parameter = ((CoreCaseExpression) expr).getParameters();
          resultType = ((CoreCaseExpression) expr).getResultType();
          levelSubst = LevelSubstitution.EMPTY;
        } else {
          throw new IllegalStateException();
        }

        boolean needSubst = false;
        List<SubstitutionPair> substitution = new ArrayList<>();
        int k = 0;
        List<TypedExpression> removedArgs = data.removedArgs;
        Set<CoreBinding> matchedParams = new HashSet<>();
        Pair<CoreParameter, CoreBinding> errorPair = null;
        for (int j = 0; j < removedArgs.size(); j++) {
          ConcreteExpression subst;
          if (removedArgs.get(j) != null) {
            subst = factory.core(removedArgs.get(j));
          } else {
            CoreBinding binding = parameter.getTypeExpr().findFreeBindings(matchedParams);
            if (binding != null) {
              errorPair = new Pair<>(parameter, binding);
              if (needSubst) break;
            }

            Integer index = data.argsReindexing.get(j);
            Pair<Integer, Integer> pair = index == null ? new Pair<>(i, k++) : findArgument(dataList, index);
            ArendRef ref = argRefs.get(new Pair<>(pair.proj1 + dataList.size() - resultDataList.size(), pair.proj2));
            if (ref != null) {
              subst = factory.ref(ref);
              needSubst = true;
              if (errorPair != null) break;
            } else {
              subst = factory.core(dataList.get(pair.proj1).matchedArgs.get(pair.proj2));
            }
            matchedParams.add(parameter.getBinding());
          }
          substitution.add(new SubstitutionPair(parameter.getBinding(), subst));
          parameter = parameter.getNext();
        }

        if (needSubst && errorPair != null) {
          errorReporter.report(new TypecheckingError("Dependent pattern matching is not supported (parameter '" + errorPair.proj1.getBinding().getName() + "' depends on '" + errorPair.proj2.getName() + "')", marker));
          return null;
        }

        ArendRef ref = factory.local(ext.renamerFactory.getNameFromType(resultType, null));
        lambdaParams.add(factory.param(ref));
        lambdaTypesParams.add(factory.param(Collections.singletonList(ref), needSubst ? factory.meta("subst_meta", new SubstitutionMeta(resultType, levelSubst, substitution)) : factory.core(data.expression.computeType().computeTyped())));
        argRefs.put(new Pair<>(i + dataList.size() - resultDataList.size(), -1), ref);
      }

      List<ArendRef> replacementRefs = new ArrayList<>(indicesToAbstract.size());
      for (Pair<Integer, Integer> pair : indicesToAbstract) {
        replacementRefs.add(argRefs.get(pair));
      }

      if (lambdaParams.isEmpty()) {
        resultLambda = expectedType.computeTyped();
      } else {
        CoreParameter lambdaTypes = typechecker.typecheckParameters(lambdaTypesParams);
        if (lambdaTypes == null) {
          return null;
        }
        resultLambda = Utils.tryTypecheck(typechecker, tc -> tc.typecheckLambda((ConcreteLamExpression) factory.lam(lambdaParams, factory.meta("case_return_lambda", new ReplaceExactSubexpressionsMeta(expectedType, expressionsToAbstract, replacementRefs))), lambdaTypes));
        if (resultLambda == null) {
          errorReporter.report(new TypeError(typechecker.getExpressionPrettifier(), "Cannot perform substitution in the expected type", expectedType, marker));
          return null;
        }
      }
      abstractedArgs = argRefs.keySet();
    }

    List<List<CorePattern>> requiredBlock = removeRedundantRows(mergeColumns(product(requiredBlocks), dataList));
    List<List<CorePattern>> refinedBlock = mergeColumns(product(refinedBlocks), dataList);

    if (additionalParameters != null) {
      List<CorePattern> additionalPatterns = new ArrayList<>();
      for (CoreParameter param = additionalParameters; param.hasNext(); param = param.getNext()) {
        additionalPatterns.add(new ArendPattern(param.getBinding(), null, Collections.emptyList(), null, ext.renamerFactory));
      }
      for (List<CorePattern> row : requiredBlock) {
        row.addAll(additionalPatterns);
      }
      for (List<CorePattern> row : refinedBlock) {
        row.addAll(additionalPatterns);
      }
    }

    if (!addPathList.isEmpty()) {
      List<CorePattern> addPathPatterns = new ArrayList<>();
      CoreParameter param = caseParams;
      for (Boolean addPath : addPathList) {
        if (addPath) {
          param = param.getNext();
          addPathPatterns.add(new ArendPattern(param.getBinding(), null, Collections.emptyList(), null, ext.renamerFactory));
        } else {
          addPathPatterns.add(null);
        }
        param = param.getNext();
      }
      insertAddPath(requiredBlock, addPathPatterns);
      insertAddPath(refinedBlock, addPathPatterns);
    }

    // Find coverings of required rows by actual rows
    Map<Integer, List<Integer>> coveringRows = new HashMap<>(); // keys are indexing requiredBlock, values are indexing actualRows
    for (int i = 0; i < requiredBlock.size(); i++) {
      List<Integer> covering = PatternUtils.computeCovering(actualRows, requiredBlock.get(i));
      if (covering != null) {
        coveringRows.put(i, covering);
      }
    }

    // If there is no default expression and not all rows are covered, report them and quit
    if (defaultExpr == null && coveringRows.size() < requiredBlock.size()) {
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
      if (defaultExpr != null) {
        errorReporter.report(new IgnoredArgumentError(defaultExpr));
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
        // This condition is equivalent to PatternUtils.refines(refinedRow, requiredBlock.get(i))
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

    // Remove addPath arguments from actualRows
    List<List<CorePattern>> actualRowsWithoutAddPath;
    if (addPathList.isEmpty()) {
      actualRowsWithoutAddPath = actualRows;
    } else {
      actualRowsWithoutAddPath = new ArrayList<>(actualRows.size());
      for (List<CorePattern> row : actualRows) {
        List<CorePattern> newRow = new ArrayList<>();
        for (int j = 0; j < row.size(); j++) {
          newRow.add(row.get(j));
          if (j < addPathList.size() && addPathList.get(j)) {
            j++;
          }
        }
        actualRowsWithoutAddPath.add(newRow);
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
          cExpr = pair.proj1 < actualClauses.size() ? actualClauses.get(pair.proj1).getExpression() : defaultExpr;
          if (cExpr == null) {
            errorReporter.report(new TypecheckingError("Clause must have a right hand side", actualClauses.get(pair.proj1)));
            return null;
          }
          if (lamParams != null) {
            List<ConcreteParameter> cParams = new ArrayList<>();
            if (pair.proj1 < actualClauses.size()) {
              List<ArendRef> refs = new ArrayList<>();
              PatternUtils.getReferences(actualClauses.get(pair.proj1).getPatterns(), refs);
              CoreParameter param = lamParams;
              for (ArendRef ref : refs) {
                cParams.add(factory.param(ref != null ? ref : factory.local(ext.renamerFactory.getNameFromBinding(param.getBinding(), null))));
                param = param.getNext();
              }
            } else {
              for (CoreParameter param = lamParams; param.hasNext(); param = param.getNext()) {
                cParams.add(factory.param(factory.local(ext.renamerFactory.getNameFromBinding(param.getBinding(), null))));
              }
            }

            Map<CoreBinding, ArendRef> bindings = new HashMap<>();
            int k = 0;
            for (CoreParameter param = lamParams; param.hasNext() && k < cParams.size(); param = param.getNext()) {
              bindings.put(param.getBinding(), cParams.get(k++).getRefList().get(0));
            }

            List<CorePattern> actualRowWithoutAddPath = actualRowsWithoutAddPath.get(pair.proj1);
            TypedExpression lamExpr = typechecker.typecheckLambda((ConcreteLamExpression) factory.lam(cParams, factory.typed(cExpr, factory.meta("c" + (resultClauses.size() + 1) + "_type", new MetaDefinition() {
              @Override
              public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
                List<ConcreteExpression> args = new ArrayList<>();
                int l = 0;
                for (int j = 0; j < dataList.size(); j++) {
                  SubexpressionData data = dataList.get(j);
                  for (int k = 0; k < data.matchedArgs.size(); k++) {
                    if (abstractedArgs.contains(new Pair<>(j, k))) {
                      args.add(PatternUtils.toExpression(actualRowWithoutAddPath.get(l + k), ext, factory, bindings));
                    }
                  }
                }

                for (SubexpressionData data : resultDataList) {
                  List<CorePattern> patternArgs = new ArrayList<>();
                  for (int k = 0; k < data.removedArgs.size(); k++) {
                    if (data.removedArgs.get(k) == null) {
                      Integer index = data.argsReindexing.get(k);
                      patternArgs.add(actualRowWithoutAddPath.get(index == null ? l++ : index));
                    } else {
                      patternArgs.add(null);
                    }
                  }
                  CoreExpression arg = PatternUtils.eval(data.body, data.levelSubst, patternArgs, data.removedArgs, typechecker, ext, factory, bindings);
                  if (arg == null) {
                    return null;
                  }
                  args.add(factory.core(arg.computeTyped()));
                }
                return args.isEmpty() ? resultLambda : typechecker.typecheck(factory.app(factory.core(resultLambda), true, args), null);
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
        List<ConcretePattern> cPatterns = PatternUtils.toConcrete(refinedRows.get(i), null, ext.renamerFactory, factory, bindings, null);
        CoreParameter param = lamParams;
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
        assert actualRow.size() >= argParamsList.size();
        List<ArendRef> asRefs = new ArrayList<>();
        for (int j = argParamsList.size(); j < actualRow.size(); j++) {
          asRefs.add(null);
        }
        for (CasesMeta.ArgParameters argParameters : argParamsList) {
          argParameters.addAsRef(asRefs);
        }
        resultClauses.add(pair.proj1 < actualClauses.size() ? actualClauses.get(pair.proj1) : factory.clause(PatternUtils.toConcrete(actualRow, asRefs, ext.renamerFactory, factory, null, null), isAbsurd ? null : defaultExpr));
      }
    }

    // Construct arguments for the resulting \case expression
    List<ConcreteCaseArgument> caseArgs = new ArrayList<>();
    List<ConcreteExpression> caseRefExprs = new ArrayList<>(dataList.size());
    List<List<ArendRef>> refLists = new ArrayList<>();
    List<List<CoreExpression>> substExprLists = new ArrayList<>();
    List<List<ArendRef>> substRefLists = new ArrayList<>();
    List<Pair<TypedExpression,Object>> substPairs = new ArrayList<>();
    int totalArgs = 0;
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
          LevelSubstitution levelSubst = dataList.get(pair.proj1).levelSubst;
          caseArgs.add(factory.caseArg(factory.core(typed), ref, factory.meta(name + "_" + (j + 1), new MetaDefinition() {
              @Override
              public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
                AbstractedExpression argType = typechecker.substituteAbstractedExpression(abstracted, levelSubst, refExprsCopy, null);
                return argType == null ? null : ((CoreExpression) argType).computeTyped();
              }
            })
          ));
          if (totalArgs < addPathList.size() && addPathList.get(totalArgs)) {
            ConcreteAppBuilder builder = factory.appBuilder(factory.ref(ext.prelude.getEqualityRef()));
            CoreExpression type = typed.getType().normalize(NormalizationMode.WHNF);
            if (type instanceof CoreDataCallExpression && ((CoreDataCallExpression) type).getDefinition() == ext.prelude.getFin()) {
              builder.app(factory.ref(ext.prelude.getNatRef()), false);
            }
            caseArgs.add(factory.caseArg(factory.ref(ext.prelude.getIdpRef()), null, builder.app(factory.core(typed)).app(factory.ref(ref)).build()));
          }
          totalArgs++;
          exprs.add(typed.getExpression());
          refs.add(ref);
          substPairs.add(new Pair<>(typed, ref));
          refList.add(ref);
          refExprs.add(refExpr);
        } else {
          List<? extends CoreExpression> originalArgs = data.getOriginalArgs();
          exprs.add(originalArgs.get(j));
          refs.add(refLists.get(pair.proj1).get(pair.proj2));
          substPairs.add(new Pair<>(originalArgs.get(j).computeTyped(), refLists.get(pair.proj1).get(pair.proj2)));
        }
      }

      refLists.add(refList);
      substExprLists.add(exprs);
      substRefLists.add(refs);
    }

    for (int i = 0; i < additionalArgs.size(); i++) {
      ArendRef ref = argParamsList.get(i).name != null ? argParamsList.get(i).name : factory.local("arg" + (i + 1));
      caseArgs.add(factory.caseArg(factory.core(additionalArgs.get(i).proj1), ref, factory.meta("case_additional_arg_" + (i + 1), new ReplaceSubexpressionsMeta(additionalArgs.get(i).proj2, substPairs))));
      if (totalArgs < addPathList.size() && addPathList.get(totalArgs)) {
        caseArgs.add(factory.caseArg(factory.ref(ext.prelude.getIdpRef()), null, factory.app(factory.ref(ext.prelude.getEqualityRef()), true, factory.core(additionalArgs.get(i).proj1), factory.ref(ref))));
      }
      totalArgs++;
      substPairs.add(new Pair<>(additionalArgs.get(i).proj1, ref));
    }

    for (int i = 0; i < dataList.size(); i++) {
      SubexpressionData data = dataList.get(i);
      List<ArendRef> refs = new ArrayList<>();
      List<CoreExpression> exprs = new ArrayList<>();
      for (int j = 0, k = 0; j < data.removedArgs.size(); j++) {
        TypedExpression removedArg = data.removedArgs.get(j);
        if (removedArg == null) {
          refs.add(substRefLists.get(i).get(k));
          exprs.add(substExprLists.get(i).get(k));
          k++;
          continue;
        }
        typechecker.withCurrentState(tc -> {
          removedArg.getExpression().processSubexpression(expr -> {
            CoreExpression exprType = expr.computeType();
            if (exprType.isError()) return CoreExpression.FindAction.CONTINUE;

            for (int i1 = 0; i1 < dataList.size(); i1++) {
              List<TypedExpression> matchedArgs = dataList.get(i1).matchedArgs;
              for (int j1 = 0; j1 < matchedArgs.size(); j1++) {
                TypedExpression arg = matchedArgs.get(j1);
                if (tc.compare(arg.getType(), exprType, CMP.EQ, marker, false, true, false) && tc.compare(arg.getExpression(), expr, CMP.EQ, marker, false, true, true)) {
                  tc.updateSavedState();
                  refs.add(refLists.get(i1).get(j1));
                  exprs.add(expr);
                } else {
                  tc.loadSavedState();
                }
              }
            }
            return CoreExpression.FindAction.CONTINUE;
          });
          return null;
        });
      }
      if (i + resultDataList.size() >= dataList.size()) {
        caseRefExprs.add(factory.meta("case_return_arg_" + (i + 1), new ReplaceExactSubexpressionsMeta(data.expression, exprs, refs)));
      }
    }

    // Typecheck the result
    ConcreteExpression result = factory.caseExpr(isSCase[0], caseArgs, factory.app(factory.core(resultLambda), true, caseRefExprs), null, resultClauses);
    return typechecker.typecheck(letClauses.isEmpty() ? result : factory.letExpr(true, false, letClauses, result), contextData.getExpectedType());
  }

  private static class ReplaceExactSubexpressionsMeta implements MetaDefinition {
    private final CoreExpression type;
    private final List<CoreExpression> subexpressions;
    private final List<ArendRef> subexpressionRefs;
    private int subexprIndex;

    private ReplaceExactSubexpressionsMeta(CoreExpression type, List<CoreExpression> subexpressions, List<ArendRef> subexpressionRefs) {
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
      }, false);
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
    Map<Integer, Set<Integer>> removedSets = new HashMap<>();
    Set<Integer> removedRows = new HashSet<>();
    for (SubexpressionData data : dataList) {
      for (int k = 0; k < data.removedArgs.size(); k++) {
        if (data.removedArgs.get(k) != null) continue;
        Integer i = data.argsReindexing.get(k);
        if (i != null) {
          for (int l = 0; l < rows.size(); l++) {
            if (removedRows.contains(l)) continue;
            List<CorePattern> row = rows.get(l);
            Map<CoreBinding, CorePattern> subst = new HashMap<>();
            if (PatternUtils.unify(row.get(i), row.get(j), subst, null)) {
              removedSets.computeIfAbsent(l, l1 -> new HashSet<>()).add(j);
              row.set(i, row.get(i).subst(subst));
            } else {
              removedRows.add(l);
            }
          }
        }
        j++;
      }
    }
    if (removedSets.isEmpty() && removedRows.isEmpty()) {
      return rows;
    }

    List<List<CorePattern>> newRows = new ArrayList<>(rows.size());
    for (int i = 0; i < rows.size(); i++) {
      if (removedRows.contains(i)) continue;
      Set<Integer> removedIndices = removedSets.get(i);
      List<CorePattern> row = rows.get(i);
      if (removedIndices == null) {
        newRows.add(row);
        continue;
      }
      List<CorePattern> newRow = new ArrayList<>();
      for (int k = 0; k < row.size(); k++) {
        CorePattern pattern = row.get(k);
        if (!removedIndices.contains(k)) newRow.add(pattern);
      }
      newRows.add(newRow);
    }
    return newRows;
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

  private static void insertAddPath(List<List<CorePattern>> rows, List<CorePattern> addPathPatterns) {
    for (int i = 0; i < rows.size(); i++) {
      List<CorePattern> row = rows.get(i);
      List<CorePattern> newRow = new ArrayList<>();
      for (int j = 0; j < row.size(); j++) {
        newRow.add(row.get(j));
        if (j < addPathPatterns.size() && addPathPatterns.get(j) != null) {
          newRow.add(addPathPatterns.get(j));
        }
      }
      rows.set(i, newRow);
    }
  }
}
