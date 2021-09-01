package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteAppBuilder;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.ExpressionMapper;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;

import org.arend.lib.meta.equation.EqualitySolver;
import org.arend.lib.meta.equation.EquationSolver;
import org.arend.lib.meta.util.SubstitutionMeta;
import org.arend.lib.util.Pair;
import org.arend.lib.util.Utils;
import org.arend.lib.error.SubexprError;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;

public class RewriteMeta extends BaseMetaDefinition {
  private final StdExtension ext;
  private final boolean isForward;
  private final boolean isInverse;
  private final boolean useEqSolver;

  public RewriteMeta(StdExtension ext, boolean isForward, boolean isInverse, boolean useEqSolver) {
    this.ext = ext;
    this.isForward = isForward;
    this.isInverse = isInverse;
    this.useEqSolver = useEqSolver;
  }

  @Override
  public boolean withoutLevels() {
    return false;
  }

  @Override
  public boolean[] argumentExplicitness() {
    return new boolean[] { false, true, true };
  }

  private void getNumber(ConcreteExpression expression, List<Integer> result, ErrorReporter errorReporter) {
    int n = Utils.getNumber(expression, errorReporter);
    if (n >= 1) {
      result.add(n - 1);
    }
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return ext.factory.appBuilder(ext.factory.ref(ext.transportInv.getRef())).app(ext.factory.hole()).app(arguments.subList(arguments.get(0).isExplicit() ? 0 : 1, arguments.size())).build();
  }

  private EquationSolver.SubexprOccurrences matchSubexpr(CoreExpression subExpr, CoreExpression expr, ExpressionTypechecker tc, ConcreteReferenceExpression refExpr, List<Integer> occurrences) {
    //if (tc.compare(subExpr, expr, CMP.EQ, refExpr, false, true)) {
    //  return ext.factory.ref(ext.equationMeta.ide.getRef());
   // }
   // if (useEqSolver) {
    var solver = new EqualitySolver(ext.equationMeta, tc, ext.factory, refExpr);
    solver.setValuesType(expr.computeType());
    solver.setUseHypotheses(false);
    solver.initializeSolver();
    var result = solver.matchSubexpr(subExpr.computeTyped(), expr.computeTyped(), tc.getErrorReporter(), occurrences);
    if (result.doesExist()) {
      result.equalityProof = ext.factory.core(solver.finalize(result.equalityProof));
      result.exprWithOccurrences = ext.factory.core(solver.finalize(result.exprWithOccurrences));
    }
    return result;
    //}
    //return null;
  }

  private class RewriteExpressionProcessor implements Function<CoreExpression, CoreExpression.FindAction> {
    private final CoreExpression subExpr;
    // private final TypedExpression occurVar;
    // private final TypedExpression exactOccurVar;
    private final ExpressionTypechecker typechecker;
    private final ConcreteReferenceExpression refExpr;
    private final CoreExpression subExprType;
    private final ConcreteFactory factory;

    // private int occurCounter = 0;
    private List<Integer> occurrences;
    private final List<Pair<EquationSolver.SubexprOccurrences, CoreExpression>> foundOccurrences = new ArrayList<>();
    private final List<Integer> exactMatches = new ArrayList<>();

    public List<Integer> getExactMatches() {
      return exactMatches;
    }

    public List<Pair<EquationSolver.SubexprOccurrences, CoreExpression>> getFoundOccurrences() {
      return foundOccurrences;
    }

    public boolean allOccurrencesFound() { return occurrences == null || occurrences.isEmpty(); }

    public RewriteExpressionProcessor(CoreExpression subExpr, CoreExpression subExprType, List<Integer> occurrences, ExpressionTypechecker typechecker, ConcreteReferenceExpression refExpr) {
      this.subExpr = subExpr;
     // this.occurVar = occurVar;
     // this.exactOccurVar = exactOccurVar;
      this.occurrences = occurrences != null ? new ArrayList<>(occurrences) : null;
      this.typechecker = typechecker;
      this.refExpr = refExpr;
      this.subExprType = subExpr.computeType(); // subExprType;
      this.factory = ext.factory.withData(refExpr.getData());
    }

    @Override
    public @Nullable CoreExpression.FindAction apply(@NotNull CoreExpression expression) {
      if (occurrences != null && occurrences.isEmpty()) return CoreExpression.FindAction.STOP;
      boolean ok;
      boolean exactMatch = false;
      boolean skip = false;
      EquationSolver.SubexprOccurrences subExprOccur = null;
      if (subExpr instanceof CoreFunCallExpression && expression instanceof CoreFunCallExpression && ((CoreFunCallExpression) subExpr).getDefinition() == ((CoreFunCallExpression) expression).getDefinition()) {
        ok = true;
        List<? extends CoreExpression> args1 = ((CoreFunCallExpression) subExpr).getDefCallArguments();
        if (args1.isEmpty()) {
          return CoreExpression.FindAction.CONTINUE;
        }
        List<? extends CoreExpression> args2 = ((CoreFunCallExpression) expression).getDefCallArguments();
        for (int i = 0; i < args1.size(); i++) {
          if (!typechecker.compare(args1.get(i), args2.get(i), CMP.EQ, refExpr, false, true)) {
            ok = false;
            break;
          }
        }
        exactMatch = true;
      } else {
        var subExprTypeFixed = subExprType;
        var expressionTypeFixed = expression.computeType();
        while (subExprTypeFixed instanceof CoreAppExpression) {
          subExprTypeFixed = ((CoreAppExpression)subExprTypeFixed).getFunction();
        }
        while (expressionTypeFixed instanceof CoreAppExpression) {
          expressionTypeFixed = ((CoreAppExpression)expressionTypeFixed).getFunction();
        }
        if (subExprTypeFixed instanceof CoreDefCallExpression) {
          if (!(expressionTypeFixed instanceof CoreDefCallExpression)) {
            ok = false;
          } else {
            ok = ((CoreDefCallExpression)subExprTypeFixed).getDefinition() == ((CoreDefCallExpression)expressionTypeFixed).getDefinition();
          }
        } else {
          ok = typechecker.compare(subExprTypeFixed, expressionTypeFixed, CMP.LE, refExpr, false, true);
        } /**/
        if (ok) {
          ok = typechecker.compare(subExpr, expression, CMP.EQ, refExpr, false, true);
          if (!ok) {
            if (useEqSolver) {
              subExprOccur = matchSubexpr(subExpr, expression, typechecker, refExpr, occurrences);
              ok = subExprOccur.doesExist();
              //if (!ok) {
              if (occurrences != null) {
                if (ok) {
                  occurrences = occurrences.subList(0, subExprOccur.numOccurrences);
                }
                if (!occurrences.isEmpty()) {
                  occurrences.set(0, occurrences.get(0) - subExprOccur.numOccurrencesSkipped);
                }
              }
              //}
              skip = true;
            }
          } else {
            exactMatch = true;
            if (occurrences != null) {
              if (occurrences.get(0) == 0) {
                occurrences.remove(0);
                var concreteExactOccurVar = factory.local("occurVar");
                subExprOccur = new EquationSolver.SubexprOccurrences(concreteExactOccurVar, factory.ref(concreteExactOccurVar), factory.ref(ext.prelude.getIdp().getRef()), 1, 0);
                subExprOccur.wrapExprWithOccurrences(factory.core(subExprType.computeTyped()), factory);
              } else {
                ok = false;
                occurrences.set(0, occurrences.get(0) - 1);
              }
            }
          }
        }
      }
      if (ok) {
        typechecker.updateSavedState();
        foundOccurrences.add(new Pair<>(subExprOccur, expression));
        if (exactMatch) {
          exactMatches.add(foundOccurrences.size() - 1);
        }
        return CoreExpression.FindAction.SKIP;
      }
      typechecker.loadSavedState();
      return skip ? CoreExpression.FindAction.SKIP : CoreExpression.FindAction.CONTINUE;
    }
  }

  /*
  private static class ReplaceSubexpressionResult {
    EquationSolver.SubexprOccurrences subExprOccur;
    UncheckedExpression newExpression;
    boolean isExactMatch;

    public ReplaceSubexpressionResult(EquationSolver.SubexprOccurrences subExprOccur, UncheckedExpression newExpression, boolean isExactMatch) {
      this.subExprOccur = subExprOccur;
      this.newExpression = newExpression;
      this.isExactMatch = isExactMatch;
    }
  }

  private ReplaceSubexpressionResult replaceSubexpression(UncheckedExpression expr, CoreExpression subExpr, TypedExpression occurVar, TypedExpression exactOccurVar, List<Integer> occurrences,
                                                                ExpressionTypechecker typechecker, ConcreteReferenceExpression refExpr) {
    var processor = new RewriteExpressionProcessor(subExpr, occurVar, exactOccurVar, occurrence, typechecker, refExpr);
    UncheckedExpression newExpr = typechecker.withCurrentState(tc -> expr.replaceSubexpressions(processor));
    var localSubExprOccur = processor.getSubExprOccur();
    if (!localSubExprOccur.doesExist()) return null;
    return new ReplaceSubexpressionResult(localSubExprOccur, newExpr, processor.isExactMatch());
  } /**/

  private ConcreteExpression chainOfTransports(ConcreteExpression transport, ConcreteExpression type, List<ConcreteExpression> eqProofs, ConcreteExpression term, ConcreteFactory factory, ExpressionTypechecker typechecker) {
    var result = term;
    var curType = typechecker.typecheck(type, null);
    boolean isInverse = ((ConcreteReferenceExpression)transport).getReferent() == ext.transportInv.getRef();

    if (curType == null) return null;

    for (int i = 0; i < eqProofs.size(); ++i) {
      if (!(curType.getExpression() instanceof CoreLamExpression)) {
        return null;
      }
      var body = ((CoreLamExpression)(curType.getExpression())).getBody();
      var param = ((CoreLamExpression)(curType.getExpression())).getParameters();
      var newType = curType;
      var typeAppLeft = factory.core(body.computeTyped());
      for (int j = i; j < eqProofs.size(); ++j) {
        var checkedEqProof = typechecker.typecheck(eqProofs.get(j), null);
        if (checkedEqProof == null) return null;
        var equality = checkedEqProof.getType().toEquality();
        if (equality == null) return null;
        var left = equality.getDefCallArguments().get(1).normalize(NormalizationMode.NF);
        var right = equality.getDefCallArguments().get(2).normalize(NormalizationMode.NF);
        if (isInverse) {
          var tmp = left;
          left = right;
          right = tmp;
        }
        if (j == i) {
          newType = typechecker.typecheck(factory.appBuilder(factory.core(newType)).app(factory.core(right.computeTyped())).build(), null);
          if (newType == null) return null;
        } else {
          typeAppLeft = factory.appBuilder(typeAppLeft).app(factory.core(left.computeTyped())).build();
        }
      }
      var transportTypeBody = typechecker.typecheck(typeAppLeft, null);
      if (transportTypeBody == null) return null;
      var transportType = typechecker.typecheck(SubstitutionMeta.makeLambda(transportTypeBody.getExpression(), param.getBinding(), factory), null);
      if (transportType == null) return null;

      result = factory.appBuilder(transport)
              .app(factory.core(transportType))
              .app(eqProofs.get(i))
              .app(result)
              .build();

      curType = newType;
    }

    return result;
  }

  /*
  private TypedExpression typeWithOccurrences(UncheckedExpression type, CoreExpression value, TypedExpression valueType, TypedExpression exactOccurrence, List<ConcreteExpression> eqProofs, List<ArendRef> occurVars, List<Integer> occurrences, int occurIndex, ConcreteExpression concretePath, ConcreteReferenceExpression refExpr, ConcreteFactory factory, ErrorReporter errorReporter, ExpressionTypechecker typechecker) {
    if (occurrences != null && occurIndex >= occurrences.size()) {
      TypedExpression checkedType = typechecker.check(type, refExpr);
      if (checkedType == null) {
        errorReporter.report(new TypecheckingError("Cannot substitute expression", refExpr));
        return null;
      }
      return checkedType;
    }
    ArendRef ref = factory.local("y" + occurVars.size());
    int occurrence = occurrences == null ? 0 : occurrences.get(occurIndex);
    final boolean[] refWasUsed = {true};
    // factory.param(true, Collections.singletonList(ref), factory.core(valueType)))
    ConcreteExpression lam = factory.lam(List.of(factory.param(ref)), factory.meta("\\lam x_v => {!}", new MetaDefinition() {
      @Override
      public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        TypedExpression var = typechecker.typecheck(factory.ref(ref), null);
        assert var != null;
        TypedExpression exactMatchVar = exactOccurrence != null ? exactOccurrence : var;
        var replRes = replaceSubexpression(type, value, var, exactMatchVar, occurrence, typechecker, refExpr);
        if (replRes == null) {
          TypedExpression checkedType = typechecker.check(type, refExpr);
          if (checkedType == null) {
            errorReporter.report(new TypecheckingError("Cannot substitute expression", refExpr));
            return null;
          }
          if (occurVars.isEmpty() || (occurrences != null && occurIndex < occurrences.size() - 1)) {
            errorReporter.report(new SubexprError(occurrences, value, null, checkedType.getExpression(), refExpr));
            return null;
          }
          refWasUsed[0] = false;
          return checkedType;
        }

        TypedExpression newExactOccurrence = exactOccurrence;
        if (replRes.isExactMatch) {
          if (exactOccurrence == null) {
            newExactOccurrence = var;
            eqProofs.add(concretePath);
            occurVars.add(ref);
          } else {
            refWasUsed[0] = false;
          }
        } else {
          occurVars.add(ref);
          // var pmapLambda = factory.lam(Collections.singletonList(factory.param(replRes.subExprOccur.occurrenceVar)), replRes.subExprOccur.exprWithOccurrence);
          var occurPathTransport = factory.appBuilder(factory.ref(ext.pmap.getRef())).app(replRes.subExprOccur.exprWithOccurrences).app(concretePath).build();
          eqProofs.add(factory.appBuilder(factory.ref(ext.concat.getRef())).app(replRes.subExprOccur.equalityProof).app(occurPathTransport).build());
        }

        var checkedType = typeWithOccurrences(replRes.newExpression, value, valueType, newExactOccurrence, eqProofs, occurVars, occurrences, occurIndex + 1, concretePath, refExpr, factory, errorReporter, typechecker);
        if (checkedType == null) {
          errorReporter.report(new TypecheckingError("Cannot substitute expression", refExpr));
          return null;
        }
        return checkedType;
      }
    }));

    var checkedLam = typechecker.typecheck(lam, null);
    if (checkedLam == null) {
      return null;
    }

    if (!refWasUsed[0]) {
      return ((CoreLamExpression)checkedLam.getExpression()).getBody().computeTyped();
    }
    return checkedLam;
  } */

  /*
  private static CoreExpression extractLamBodyAndParams(CoreExpression expr, List<CoreParameter> params, int numberOfParams) {
    while (expr instanceof CoreLamExpression && numberOfParams > 0) {
      var lam = (CoreLamExpression)expr;
      expr = lam.getBody();
      params.add(lam.getParameters());
      --numberOfParams;
    }
    return expr;
  } /**/

  @Override
  public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    int currentArg = 0;
    ConcreteExpression occurrencesArg = args.get(0).isExplicit() ? null : args.get(currentArg++).getExpression();
    List<? extends ConcreteExpression> args0 = Utils.getArgumentList(args.get(currentArg++).getExpression());
    if (args0.isEmpty()) {
      return typechecker.typecheck(args.get(currentArg).getExpression(), contextData.getExpectedType());
    }

    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    if (args0.size() > 1) {
      ConcreteExpression result = args.get(currentArg++).getExpression();
      for (int i = args0.size() - 1; i >= 0; i--) {
        ConcreteAppBuilder builder = factory.appBuilder(refExpr);
        if (occurrencesArg != null) builder.app(occurrencesArg, false);
        result = builder.app(args0.get(i)).app(result).build();
      }
      return typechecker.typecheck(factory.app(result, args.subList(currentArg, args.size())), contextData.getExpectedType());
    }
    ConcreteExpression arg0 = args0.get(0);

    // Collect occurrences
    List<Integer> occurrences;
    if (occurrencesArg != null) {
      occurrences = new ArrayList<>();
      for (ConcreteExpression expr : Utils.getArgumentList(occurrencesArg)) {
        getNumber(expr, occurrences, errorReporter);
      }
    } else {
      occurrences = null;
    }

    CoreExpression expectedType = contextData.getExpectedType() == null ? null : contextData.getExpectedType().getUnderlyingExpression();
    boolean reverse = expectedType == null || args.size() > currentArg + 2;
    boolean isForward = reverse || this.isForward;
    //noinspection SimplifiableConditionalExpression
    boolean isInverse = reverse && !this.isForward ? !this.isInverse : this.isInverse;

    // Add inference holes to functions and type-check the path argument
    TypedExpression path = Utils.typecheckWithAdditionalArguments(arg0, typechecker, ext, 0, false);
    if (path == null) {
      return null;
    }

    // Check that the first argument is a path
    CoreFunCallExpression eq = Utils.toEquality(path.getType(), errorReporter, arg0);
    if (eq == null) {
      return null;
    }

    ConcreteExpression transport = factory.ref((isInverse ? ext.transportInv : ext.transport).getRef(), refExpr.getPLevels(), refExpr.getHLevels());
    CoreExpression value = eq.getDefCallArguments().get(isInverse == isForward ? 2 : 1);

    // This case won't happen often, but sill possible
    if (!isForward && expectedType instanceof CoreInferenceReferenceExpression) {
      CoreExpression var = value.getUnderlyingExpression();
      if (var instanceof CoreInferenceReferenceExpression && ((CoreInferenceReferenceExpression) var).getVariable() == ((CoreInferenceReferenceExpression) expectedType).getVariable()) {
        if (!(occurrences == null || occurrences.isEmpty() || occurrences.size() == 1 && occurrences.contains(1))) {
          occurrences.remove(1);
          errorReporter.report(new SubexprError(occurrences, var, null, expectedType, refExpr));
          return null;
        }
        ArendRef ref = factory.local("T");
        return typechecker.typecheck(factory.app(transport, true, Arrays.asList(
          factory.lam(Collections.singletonList(factory.param(ref)), factory.ref(ref)),
          factory.core("transport (\\lam T => T) {!} _", path),
          args.get(currentArg).getExpression())), null);
      }
      isForward = true;
    }

    TypedExpression lastArg;
    CoreExpression type;
    if (isForward) {
      lastArg = typechecker.typecheck(args.get(currentArg++).getExpression(), null);
      if (lastArg == null) {
        return null;
      }
      type = lastArg.getType();
    } else {
      lastArg = null;
      type = expectedType;
    }
    ConcreteExpression concretePath = factory.core(path);
    CoreExpression normType = type.normalize(NormalizationMode.RNF);
    ConcreteExpression term = lastArg == null ? args.get(currentArg++).getExpression() : factory.core("transport _ _ {!}", lastArg);
    var occurVars = new ArrayList<ArendRef>();
    var eqProofs = new ArrayList<ConcreteExpression>();

    // var typeWOccur = typeWithOccurrences(normType, value, eq.getDefCallArguments().get(0).computeTyped(), null, eqProofs, occurVars, occurrences, 0, concretePath, refExpr, factory, errorReporter, typechecker);

    //if (typeWOccur == null) {
    //  return null;
    //}

    var processor = new RewriteExpressionProcessor(value, eq.getDefCallArguments().get(0), occurrences, typechecker, refExpr);
    typechecker.withCurrentState(tc -> normType.processSubexpression(processor));

    var foundOccurs = processor.getFoundOccurrences();
    int firstExactMatch = processor.getExactMatches().isEmpty() ? -1 : processor.getExactMatches().get(0);

    if (foundOccurs.isEmpty() || !processor.allOccurrencesFound()) {
      errorReporter.report(new SubexprError(occurrences, value, null, normType, refExpr));
      return null;
    }

    for (int i = 0; i < foundOccurs.size(); ++i) {
      boolean isExactMatch = processor.getExactMatches().contains(i);
      if (i <= firstExactMatch || !isExactMatch) {
        var var = factory.local("y" + i);
        occurVars.add(var);
        if (isExactMatch) {
          eqProofs.add(concretePath);
        } else {
          var subExprOccur = foundOccurs.get(i).proj1;
          var occurPathTransport = factory.appBuilder(factory.ref(ext.pmap.getRef())).app(subExprOccur.exprWithOccurrences).app(concretePath).build();
          eqProofs.add(factory.appBuilder(factory.ref(ext.concat.getRef())).app(subExprOccur.equalityProof).app(occurPathTransport).build());
        }
      }
    }

    ConcreteExpression lam = factory.lam(Collections.singletonList(factory.param(true, occurVars, factory.core(eq.getDefCallArguments().get(0).computeTyped()))), factory.meta("\\lam y_v => {!}", new MetaDefinition() {
      @Override
      public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        List<TypedExpression> checkedVars = new ArrayList<>();

        for (var var : occurVars) {
          var checkedVar =  typechecker.typecheck(factory.ref(var), null);
          assert checkedVar != null;
          checkedVars.add(checkedVar);
        }

        Map<CoreExpression, Integer> indexOfSubExpr = new HashMap<>();

        for (int i = 0; i < foundOccurs.size(); ++i) {
          indexOfSubExpr.put(foundOccurs.get(i).proj2, i);
        }

        // TypedExpression exactMatchVar = finalExactMatchParam != null ? typechecker.typecheck(factory.ref(finalExactMatchParam.getBinding()), null) : var;
        var typeWithOccur = normType.replaceSubexpressions(expression -> {
          Integer index = indexOfSubExpr.get(expression);
          if (index == null) return null;
          return checkedVars.get(index).getExpression();
        });

        TypedExpression result = typeWithOccur != null ? Utils.tryTypecheck(typechecker, tc -> tc.check(typeWithOccur, refExpr)) : null;
        if (result == null) {
          errorReporter.report(new SubexprError(occurrences, value, null, normType, refExpr));
        }
        return result;
      }
    }));

    var checkedLam = typechecker.typecheck(lam, null);

    if (checkedLam == null) {
      return null;
    }

    /*
    CoreParameter exactMatchParam = null;
    int v = 0;

    while (true) {
      ArendRef ref = factory.local("y" + v);
      int occurrence = occurrences == null ? 0 : occurrences.get(v);
      CoreExpression finalNormType = normType;
      final boolean[] substWasMade = {false};
      final boolean[] typecheckErrorOccurred = {false};
      final boolean[] isExactMatch = {false};

      // CoreParameter finalExactMatchParam = exactMatchParam;
      ConcreteExpression lam = factory.lam(Collections.singletonList(factory.param(true, Collections.singletonList(ref), factory.core(eq.getDefCallArguments().get(0).computeTyped()))), factory.meta("\\lam x_v => {!}", new MetaDefinition() {
        @Override
        public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          TypedExpression var = typechecker.typecheck(factory.ref(ref), null);
          assert var != null;
          // TypedExpression exactMatchVar = finalExactMatchParam != null ? typechecker.typecheck(factory.ref(finalExactMatchParam.getBinding()), null) : var;
          var replRes = replaceSubexpression(finalNormType, value, var, occurrence, typechecker, refExpr);
          if (replRes == null) return finalNormType.computeTyped();

          substWasMade[0] = true;
          if (replRes.isExactMatch) {
            isExactMatch[0] = true;
            //if (finalExactMatchParam == null) {
              eqProofs.add(concretePath);
            //}
          } else {
            // var pmapLambda = factory.lam(Collections.singletonList(factory.param(replRes.subExprOccur.occurrenceVar)), replRes.subExprOccur.exprWithOccurrence);
            var occurPathTransport = factory.appBuilder(factory.ref(ext.pmap.getRef())).app(replRes.subExprOccur.exprWithOccurrence).app(concretePath).build();
            eqProofs.add(factory.appBuilder(factory.ref(ext.concat.getRef())).app(replRes.subExprOccur.equalityProof).app(occurPathTransport).build());
          }

          TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.check(replRes.newExpression, refExpr));
          if (result == null) {
            errorReporter.report(new SubexprError(occurrences, value, null, finalNormType, refExpr));
            typecheckErrorOccurred[0] = true;
          }
          return result;
        }
      }));

      var checkedLam = typechecker.typecheck(lam, null);

      if (typecheckErrorOccurred[0]) return null;

      if (v == 0 && !substWasMade[0]) {
        errorReporter.report(new TypecheckingError("Cannot substitute expression", refExpr));
        return null;
      }

      if (checkedLam == null) return null;

      if (!substWasMade[0]) {
        break;
      }

      normType = checkedLam.getExpression();
      if (isExactMatch[0]) {
        if (exactMatchParam == null) {
          exactMatchParam = ((CoreLamExpression) checkedLam.getExpression()).getParameters();
        }
        //else {
           //var body = ((CoreLamExpression)normType).getBody();
          //var param = ((CoreLamExpression)normType).getParameters();
          // var allParams = new ArrayList<CoreParameter>();
          //var body = extractLamBodyAndParams(normType, allParams, eqProofs.size());
          //var paramToReplace = allParams.get(0);
          //body.substitute(Collections.singletonMap(param.getBinding(), exactMatchParam.getBinding().makeReference()));
          //var concreteNormType = factory.core(body.computeTyped()).substitute(Collections.singletonMap(factory.ref(param.getBinding()).getReferent(), factory.ref(exactMatchParam.getBinding())));
          // typechecker.substitute()
          // AbstractedExpression
          //var normTypeWORedundantParam = typechecker.substituteAbstractedExpression(((CoreLamExpression)normType).getAbstractedBody(), LevelSubstitution.EMPTY, Collections.singletonList(factory.ref(param.getBinding())));
                  //typechecker.check(body.substitute(Collections.singletonMap(param.getBinding(), exactMatchParam.getBinding().makeReference())), factory.core(body.computeType().computeTyped()));// typechecker.typecheck(concreteNormType, null);
          //if (normTypeWORedundantParam == null) return null;
          //normType = normTypeWORedundantParam.getExpression();
        //}
      }

      ++v;
      if (occurrences != null && v >= occurrences.size()) break;
    }

    if (occurrences != null && eqProofs.size() != occurrences.size()) {
      errorReporter.report(new SubexprError(occurrences, value, null, type, refExpr));
      return null;
    } */

    // Collections.reverse(eqProofs);
    term = chainOfTransports(transport, factory.core(checkedLam), eqProofs, term, factory, typechecker);

    if (term == null) return null;

    term = factory.appBuilder(term)
            .app(args.subList(currentArg, args.size()))
            .build();

    return typechecker.typecheck(term, expectedType);
  }
}
