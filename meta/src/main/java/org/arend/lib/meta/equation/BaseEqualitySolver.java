package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.util.Maybe;
import org.jetbrains.annotations.Nullable;

import java.util.Arrays;

public abstract class BaseEqualitySolver implements EquationSolver {
  protected final EquationMeta meta;
  protected final ExpressionTypechecker typechecker;
  protected final ConcreteFactory factory;
  protected final ConcreteReferenceExpression refExpr;
  protected CoreFunCallExpression equality;

  protected BaseEqualitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr) {
    this.meta = meta;
    this.typechecker = typechecker;
    this.factory = factory;
    this.refExpr = refExpr;
  }

  @Override
  public boolean isApplicable(CoreExpression type) {
    return true;
  }

  @Override
  public CoreExpression getValuesType() {
    return equality.getDefCallArguments().get(0);
  }

  @Override
  public CoreExpression getLeftValue() {
    return equality == null ? null : equality.getDefCallArguments().get(1);
  }

  @Override
  public CoreExpression getRightValue() {
    return equality == null ? null : equality.getDefCallArguments().get(2);
  }

  @Override
  public @Nullable Maybe<CoreExpression> getEqType(@Nullable TypedExpression leftExpr, @Nullable TypedExpression rightExpr) {
    if (leftExpr != null && rightExpr != null) {
      TypedExpression result = typechecker.typecheck(factory.app(factory.ref(meta.ext.prelude.getEquality().getRef()), true, Arrays.asList(factory.core(leftExpr), factory.core(rightExpr))), null);
      return result == null ? null : new Maybe<>(result.getExpression());
    } else {
      return new Maybe<>(null);
    }
  }

  @Override
  public TypedExpression getTrivialResult(TypedExpression expression) {
    return typechecker.typecheck(factory.app(factory.ref(meta.ext.prelude.getIdp().getRef()), false, Arrays.asList(factory.hole(), factory.core(expression))), null);
  }

  @Override
  public ConcreteExpression combineResults(ConcreteExpression expr1, ConcreteExpression expr2) {
    return factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(expr1, expr2));
  }

  @Override
  public boolean isHint(ConcreteExpression expression) {
    return ContextHelper.getMeta(expression) != null;
  }

  @Override
  public boolean initializeSolver() {
    return true;
  }
}
