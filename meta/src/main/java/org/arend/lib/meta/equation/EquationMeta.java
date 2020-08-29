package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.ListErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Maybe;
import org.arend.lib.error.TypeError;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class EquationMeta extends BaseMetaDefinition {
  final StdExtension ext;

  @Dependency(module = "Set")                     public CoreClassDefinition BaseSet;
  @Dependency(module = "Set", name = "BaseSet.E") public CoreClassField carrier;

  @Dependency(module = "Algebra.Pointed")                          public CoreClassDefinition Pointed;
  @Dependency(module = "Algebra.Pointed")                          public CoreClassDefinition AddPointed;
  @Dependency(module = "Algebra.Pointed", name = "Pointed.ide")    public CoreClassField ide;
  @Dependency(module = "Algebra.Pointed", name = "AddPointed.zro") public CoreClassField zro;

  @Dependency(module = "Algebra.Monoid")                       CoreClassDefinition Monoid;
  @Dependency(module = "Algebra.Monoid", name = "Monoid.*")    CoreClassField mul;
  @Dependency(module = "Algebra.Monoid", name = "Monoid.LDiv") CoreClassDefinition ldiv;
  @Dependency(module = "Algebra.Monoid", name = "Monoid.RDiv") CoreClassDefinition rdiv;
  @Dependency(module = "Algebra.Monoid", name = "AddMonoid.+") public CoreClassField plus;

  @Dependency(module = "Algebra.Monoid.Solver", name = "MonoidTerm.var")  CoreConstructor varTerm;
  @Dependency(module = "Algebra.Monoid.Solver", name = "MonoidTerm.:ide") CoreConstructor ideTerm;
  @Dependency(module = "Algebra.Monoid.Solver", name = "MonoidTerm.:*")   CoreConstructor mulTerm;

  @Dependency(module = "Algebra.Monoid.Solver")                                    CoreClassDefinition Data;
  @Dependency(module = "Algebra.Monoid.Solver", name = "Data.terms-equality")      CoreFunctionDefinition termsEq;
  @Dependency(module = "Algebra.Monoid.Solver", name = "Data.terms-equality-conv") CoreFunctionDefinition termsEqConv;
  @Dependency(module = "Algebra.Monoid.Solver", name = "Data.replace-consistent")  CoreFunctionDefinition replaceDef;

  @Dependency(module = "Algebra.Group", name = "AddGroup.negative") public CoreClassField negative;
  @Dependency(module = "Algebra.Semiring")                          public CoreClassDefinition Semiring;
  @Dependency(module = "Algebra.Ring")                              public CoreClassDefinition Ring;

  @Dependency(module = "Equiv")                 CoreClassDefinition Equiv;
  @Dependency(module = "Equiv", name = "Map.A") CoreClassField equivLeft;
  @Dependency(module = "Equiv", name = "Map.B") CoreClassField equivRight;
  @Dependency(module = "Equiv")                 CoreFunctionDefinition idEquiv;
  @Dependency(module = "Equiv")                 CoreFunctionDefinition transEquiv;

  public static class TransitivityInstanceCache {
    public final CoreFunctionDefinition instance;
    public final CoreClassField relationField;

    public TransitivityInstanceCache(CoreFunctionDefinition instance, CoreClassField relationField) {
      this.instance = instance;
      this.relationField = relationField;
    }
  }

  public final Map<CoreDefinition, TransitivityInstanceCache> transitivityInstanceCache = new HashMap<>();

  public EquationMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());

    // values will contain ConcreteExpression (which correspond to implicit arguments) and TypedExpression (which correspond to explicit arguments).
    List<Object> values = new ArrayList<>();

    EquationSolver solver = null;
    if (contextData.getExpectedType() != null) {
      CoreExpression type = contextData.getExpectedType().normalize(NormalizationMode.WHNF);
      final List<EquationSolver> solvers = Arrays.asList(new EqualitySolver(this, typechecker, factory, refExpr), new EquivSolver(this, typechecker, factory), new TransitivitySolver(this, typechecker, factory, refExpr));
      for (EquationSolver eqSolver : solvers) {
        if (eqSolver.isApplicable(type)) {
          solver = eqSolver;
          break;
        }
      }
      if (solver == null) {
        errorReporter.report(new TypeError("Unrecognized type", type, refExpr));
        return null;
      }
    } else {
      solver = new DefaultEquationSolver(this, typechecker, factory, refExpr);
    }

    for (ConcreteArgument argument : contextData.getArguments()) {
      if (argument.isExplicit()) {
        TypedExpression value = typechecker.typecheck(argument.getExpression(), solver.getValuesType());
        if (value == null) {
          return null;
        }
        values.add(value);
      } else {
        values.add(argument.getExpression());
      }
    }

    CoreExpression leftExpr = solver.getLeftValue();
    if (leftExpr != null && (values.isEmpty() || !(values.get(0) instanceof TypedExpression) || !Utils.safeCompare(typechecker, leftExpr, ((TypedExpression) values.get(0)).getExpression(), CMP.EQ, refExpr, false, true))) {
      values.add(0, leftExpr.computeTyped());
    }
    CoreExpression rightExpr = solver.getRightValue();
    if (rightExpr != null && (values.isEmpty() || !(values.get(values.size() - 1) instanceof TypedExpression) || !Utils.safeCompare(typechecker, rightExpr, ((TypedExpression) values.get(values.size() - 1)).getExpression(), CMP.EQ, refExpr, false, true))) {
      values.add(rightExpr.computeTyped());
    }

    // If values.size() <= 1, then we don't have expected type
    if (values.isEmpty()) {
      errorReporter.report(new TypecheckingError("Cannot infer type of the expression", refExpr));
      return null;
    }

    // If values.size() == 1, we either return the implicit argument or the trivial answer on the explicit argument
    if (values.size() == 1) {
      return values.get(0) instanceof ConcreteExpression
        ? typechecker.typecheck((ConcreteExpression) values.get(0), null)
        : solver.getTrivialResult((TypedExpression) values.get(0));
    }

    boolean hasMissingProofs = false;
    for (int i = 0; i < values.size(); i++) {
      if (values.get(i) instanceof TypedExpression && i + 1 < values.size() && values.get(i + 1) instanceof TypedExpression) {
        hasMissingProofs = true;
      } else if (values.get(i) instanceof ConcreteExpression) {
        ConcreteExpression expr = (ConcreteExpression) values.get(i);
        if (solver.isHint(expr instanceof ConcreteGoalExpression ? ((ConcreteGoalExpression) expr).getExpression() : expr)) {
          if (i > 0 && values.get(i - 1) instanceof TypedExpression && i + 1 < values.size() && values.get(i + 1) instanceof TypedExpression) {
            hasMissingProofs = true;
          } else {
            errorReporter.report(new TypecheckingError("Hints must be between explicit arguments", (ConcreteExpression) values.get(i)));
            values.remove(i--);
          }
        }
      }
    }

    if (hasMissingProofs) {
      if (solver instanceof DefaultEquationSolver && contextData.getExpectedType() == null) {
        for (Object value : values) {
          if (value instanceof TypedExpression) {
            ((DefaultEquationSolver) solver).setValuesType(((TypedExpression) value).getType());
            break;
          }
        }
      }

      if (!solver.initializeSolver()) {
        errorReporter.report(new TypecheckingError("Cannot infer missing proofs", refExpr));
        return null;
      }
    }

    boolean ok = true;
    List<ConcreteExpression> equalities = new ArrayList<>();
    for (int i = 0; i < values.size(); i++) {
      Object value = values.get(i);
      if (value instanceof ConcreteExpression && solver.isHint((ConcreteExpression) value) || value instanceof TypedExpression && i + 1 < values.size() && values.get(i + 1) instanceof TypedExpression) {
        ConcreteGoalExpression goalExpr = value instanceof ConcreteGoalExpression ? (ConcreteGoalExpression) value : null;
        List<GeneralError> errors = goalExpr != null ? new ArrayList<>() : null;
        ConcreteExpression result = solver.solve(
            goalExpr != null ? goalExpr.getExpression() : value instanceof ConcreteExpression ? (ConcreteExpression) value : null,
            (TypedExpression) values.get(value instanceof ConcreteExpression ? i - 1 : i),
            (TypedExpression) values.get(i + 1),
            errors != null ? new ListErrorReporter(errors) : errorReporter);
        if (result == null && goalExpr == null) {
          ok = false;
          continue;
        }
        equalities.add(goalExpr == null ? result : factory.withData(goalExpr.getData()).goal(goalExpr.getName(), result, null, Objects.requireNonNull(errors)));
      } else if (value instanceof ConcreteExpression) {
        Maybe<CoreExpression> eqType = solver.getEqType(
            i > 0 && values.get(i - 1) instanceof TypedExpression ? (TypedExpression) values.get(i - 1) : null,
            i < values.size() - 1 && values.get(i + 1) instanceof TypedExpression ? (TypedExpression) values.get(i + 1) : null);

        TypedExpression result = eqType == null ? null : typechecker.typecheck((ConcreteExpression) value, eqType.just);
        if (result == null) {
          ok = false;
        } else {
          equalities.add(factory.core(null, result));
        }
      }
    }
    if (!ok) {
      return null;
    }

    ConcreteExpression result = equalities.get(equalities.size() - 1);
    for (int i = equalities.size() - 2; i >= 0; i--) {
      result = solver.combineResults(equalities.get(i), result);
    }
    return hasMissingProofs ? solver.finalize(result) : typechecker.typecheck(result, null);
  }
}
