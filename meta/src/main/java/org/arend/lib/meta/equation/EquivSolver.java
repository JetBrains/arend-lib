package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.util.Maybe;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class EquivSolver implements EquationSolver {
  private final EquationMeta meta;
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;

  private CoreClassCallExpression classCall;

  public EquivSolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory) {
    this.meta = meta;
    this.typechecker = typechecker;
    this.factory = factory;
  }

  @Override
  public boolean isApplicable(CoreExpression type) {
    if (!(type instanceof CoreClassCallExpression && ((CoreClassCallExpression) type).getDefinition().isSubClassOf(meta.Equiv))) {
      return false;
    }
    classCall = (CoreClassCallExpression) type;
    return true;
  }

  @Override
  public CoreExpression getValuesType() {
    return null;
  }

  @Override
  public CoreExpression getLeftValue() {
    return classCall.getClosedImplementation(meta.equivLeft);
  }

  @Override
  public CoreExpression getRightValue() {
    return classCall.getClosedImplementation(meta.equivRight);
  }

  @Override
  public @Nullable Maybe<CoreExpression> getEqType(@Nullable TypedExpression leftExpr, @Nullable TypedExpression rightExpr) {
    ConcreteExpression expr = factory.ref(meta.Equiv.getRef());
    if (leftExpr != null || rightExpr != null) {
      List<ConcreteExpression> args = new ArrayList<>(2);
      if (leftExpr != null) {
        args.add(factory.core(null, leftExpr));
      }
      if (rightExpr != null) {
        args.add(factory.core(null, rightExpr));
      }
      expr = factory.app(expr, false, args);
    }
    TypedExpression result = typechecker.typecheck(expr, null);
    return result == null ? null : new Maybe<>(result.getExpression());
  }

  @Override
  public TypedExpression getTrivialResult(TypedExpression expression) {
    return typechecker.typecheck(factory.app(factory.ref(meta.idEquiv.getRef()), false, Collections.singletonList(factory.core(null, expression))), null);
  }

  @Override
  public ConcreteExpression combineResults(ConcreteExpression expr1, ConcreteExpression expr2) {
    return factory.app(factory.ref(meta.transEquiv.getRef()), true, Arrays.asList(expr1, expr2));
  }

  @Override
  public boolean isHint(ConcreteExpression expression) {
    return false;
  }

  @Override
  public boolean initializeSolver() {
    return false;
  }

  @Override
  public ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter) {
    return null;
  }

  @Override
  public SubexprOccurrences matchSubexpr(@NotNull TypedExpression subExpr, @NotNull TypedExpression expr, @NotNull ErrorReporter errorReporter, List<Integer> occurrences) {
    return null;
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    return null;
  }
}
