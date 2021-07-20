package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;

import org.arend.lib.meta.equation.EqualitySolver;
import org.arend.lib.meta.util.SubstitutionMeta;
import org.arend.lib.util.Pair;
import org.arend.lib.util.Utils;
import org.arend.lib.error.SubexprError;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

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

  private void getNumber(ConcreteExpression expression, Set<Integer> result, ErrorReporter errorReporter) {
    int n = Utils.getNumber(expression, errorReporter);
    if (n >= 0) {
      result.add(n);
    }
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return ext.factory.appBuilder(ext.factory.ref(ext.transportInv.getRef())).app(ext.factory.hole()).app(arguments.subList(arguments.get(0).isExplicit() ? 0 : 1, arguments.size())).build();
  }

  private ConcreteExpression smartEqualityCheck(CoreExpression expr1, CoreExpression expr2, ExpressionTypechecker tc, ConcreteReferenceExpression refExpr) {
    if (tc.compare(expr1, expr2, CMP.EQ, refExpr, false, true)) {
      return ext.factory.ref(ext.equationMeta.ide.getRef());
    }
    if (useEqSolver) {
      var solver = new EqualitySolver(ext.equationMeta, tc, ext.factory, refExpr);
      solver.setValuesType(expr2.computeType());
      solver.setUseHypotheses(false);
      solver.initializeSolver();
      var result = solver.solve(null, expr1.computeTyped(), expr2.computeTyped(), tc.getErrorReporter());
      if (result == null)  return null;
      return ext.factory.core(solver.finalize(result));
    }
    return null;
  }

  private Pair<UncheckedExpression, ConcreteExpression> replaceSubexpression(CoreExpression expr, CoreExpression subExpr, TypedExpression var, Set<Integer> occurrences, boolean exactMatch,
                                                                            ExpressionTypechecker typechecker, ConcreteReferenceExpression refExpr) {
    final int[] num = {0};
    CoreExpression subExprType = subExpr.computeType();
    AtomicReference<ConcreteExpression> equalityProof = new AtomicReference<>(null);
    AtomicBoolean changedExpr = new AtomicBoolean(false);
    UncheckedExpression newExpr = typechecker.withCurrentState(tc -> expr.replaceSubexpressions(expression -> {
      boolean ok;
      if (changedExpr.get() && !exactMatch) {
        return null;
      }
      if (subExpr instanceof CoreFunCallExpression && expression instanceof CoreFunCallExpression && ((CoreFunCallExpression) subExpr).getDefinition() == ((CoreFunCallExpression) expression).getDefinition()) {
        ok = true;
        List<? extends CoreExpression> args1 = ((CoreFunCallExpression) subExpr).getDefCallArguments();
        if (args1.isEmpty()) {
          return null;
        }
        List<? extends CoreExpression> args2 = ((CoreFunCallExpression) expression).getDefCallArguments();
        for (int i = 0; i < args1.size(); i++) {
          if (!tc.compare(args1.get(i), args2.get(i), CMP.EQ, refExpr, false, true)) {
            ok = false;
            break;
          }
        }
      } else {
        ok = tc.compare(subExprType, expression.computeType(), CMP.LE, refExpr, false, true);
        if (ok) {
          if (exactMatch || !useEqSolver) {
            ok = tc.compare(expression, subExpr, CMP.EQ, refExpr, false, true);
            // If we are in useEqSolver regime and are looking for exact matches still should not forget to
            // increment occurrences counter. Warning: will behave weirdly for nested equal subsexpressions!
            if (!ok && useEqSolver && smartEqualityCheck(expression, subExpr, tc, refExpr) != null) {
              num[0]++;
            }
          } else {
            equalityProof.set(smartEqualityCheck(expression, subExpr, tc, refExpr));
            ok = equalityProof.get() != null;
          }
        }
      }
      if (ok) {
        num[0]++;
        if (occurrences == null || occurrences.contains(num[0])) {
          if (occurrences != null) occurrences.remove(num[0]);
          changedExpr.set(true);
          tc.updateSavedState();
          return var.getExpression();
        }
      }
      tc.loadSavedState();
      return null;
    }));
    if (!changedExpr.get()) return new Pair<>(null, null);
    return new Pair<>(newExpr, equalityProof.get());
  }

  @Override
  public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    List<? extends ConcreteArgument> args = contextData.getArguments();
    int currentArg = 0;

    // Collect occurrences
    Set<Integer> occurrences;
    if (!args.get(0).isExplicit()) {
      occurrences = new HashSet<>();
      for (ConcreteExpression expr : Utils.getArgumentList(args.get(0).getExpression())) {
        getNumber(expr, occurrences, errorReporter);
      }
      currentArg++;
    } else {
      occurrences = null;
    }

    CoreExpression expectedType = contextData.getExpectedType() == null ? null : contextData.getExpectedType().getUnderlyingExpression();
    boolean reverse = expectedType == null || args.size() > currentArg + 2;
    boolean isForward = reverse || this.isForward;
    //noinspection SimplifiableConditionalExpression
    boolean isInverse = reverse && !this.isForward ? !this.isInverse : this.isInverse;

    // Add inference holes to functions and type-check the path argument
    ConcreteExpression arg0 = args.get(currentArg++).getExpression();
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
    CoreExpression normType = type.normalize(NormalizationMode.RNF);
    ConcreteExpression term = lastArg == null ? args.get(currentArg++).getExpression() : factory.core("transport _ _ {!}", lastArg);
    var eqProofs = new ArrayList<ConcreteExpression>();
    var typePrefixes = new ArrayList<ConcreteExpression>();
    int v = 0;
    boolean exactMatch = true;
    final boolean[] nothingChanged = {false};

    while (true) {
      ArendRef ref = factory.local("y" + v);
      final boolean[] typecheckErrorOccurred = {false};
      CoreExpression finalNormType = normType;

      boolean finalExactMatch = exactMatch;
      ConcreteExpression lam = factory.lam(Collections.singletonList(factory.param(true, Collections.singletonList(ref), factory.core(eq.getDefCallArguments().get(0).computeTyped()))), factory.meta("\\lam x_v => {!}", new MetaDefinition() {
        @Override
        public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          TypedExpression var = typechecker.typecheck(factory.ref(ref), null);
          assert var != null;
          var replacementRes = replaceSubexpression(finalNormType, value, var, occurrences, finalExactMatch, typechecker, refExpr);
          UncheckedExpression absNewType = replacementRes.proj1;
          ConcreteExpression eqProof = replacementRes.proj2;
          boolean prevNothingChanged = nothingChanged[0];

          nothingChanged[0] = absNewType == null;
          if (nothingChanged[0]) {
            if (!useEqSolver || (!finalExactMatch && prevNothingChanged)) {
              errorReporter.report(new TypecheckingError("Cannot substitute expression", refExpr));
              typecheckErrorOccurred[0] = true;
              return null;
            }
            return finalNormType.computeTyped();
          }

          ConcreteExpression concretePath = factory.core(path);
          if (eqProof == null) {
            eqProofs.add(concretePath);
          } else {
            eqProofs.add(factory.appBuilder(factory.ref(ext.concat.getRef())).app(eqProof).app(concretePath).build());
          }

          TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.check(absNewType, refExpr));
          if (result == null) {
            errorReporter.report(new SubexprError(occurrences, value, null, finalNormType, refExpr));
          }

          return result;
        }
      }));

      var checkedLam = typechecker.typecheck(lam, null);

      if (typecheckErrorOccurred[0] || checkedLam == null) return null;
      if (nothingChanged[0]) {
        if (!exactMatch || !useEqSolver) {
          --v;
          break;
        }
        exactMatch = false;
        continue;
      }
      if (v == 0) {
        typePrefixes.add(factory.core(checkedLam.getExpression().computeTyped()));
      }

      if (v > 0) {
        var body = ((CoreLamExpression)checkedLam.getExpression()).getBody();
        var param = ((CoreLamExpression)checkedLam.getExpression()).getParameters();
        ConcreteExpression typeAppRight = factory.core(body.computeTyped());
        for (int i = v - 1; i >= 0; --i) {
          var checkedEqProof = typechecker.typecheck(eqProofs.get(i), null);
          if (checkedEqProof == null) return null;
          var equality = checkedEqProof.getType().toEquality();
          if (equality == null) return null;
          var right = equality.getDefCallArguments().get(2);
          typeAppRight = factory.appBuilder(typeAppRight).app(factory.core(right.computeTyped())).build();
        }
        var typePrefixBody = typechecker.typecheck(typeAppRight, null);
        if (typePrefixBody == null) return null;
        var typePrefix = typechecker.typecheck(SubstitutionMeta.makeLambda(typePrefixBody.getExpression(), param.getBinding(), factory), null);
        if (typePrefix == null) return null;
        typePrefixes.add(factory.core(typePrefix));
      } /**/
      normType = checkedLam.getExpression();
      if (!useEqSolver) break;
      ++v;
      exactMatch = false;
    }

    if (occurrences != null && !occurrences.isEmpty()) {
      errorReporter.report(new SubexprError(occurrences, value, null, type, refExpr));
      return null;
    }

    for (int i = v; i >= 0; --i) {
      term = factory.appBuilder(transport)
              .app(typePrefixes.get(i))
              .app(eqProofs.get(i))
              .app(term)
              .app(args.subList(currentArg, args.size()))
              .build();
    }

    return typechecker.typecheck(term, expectedType);
  }
}
