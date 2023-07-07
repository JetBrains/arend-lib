package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.util.Maybe;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static java.util.Collections.singletonList;

public abstract class BaseEqualitySolver implements EquationSolver {
  protected final EquationMeta meta;
  protected final ExpressionTypechecker typechecker;
  protected final ConcreteFactory factory;
  protected final ConcreteReferenceExpression refExpr;
  protected CoreFunCallExpression equality;
  protected final TypedExpression instance;
  protected final Values<CoreExpression> values;
  protected final ArendRef dataRef;
  protected boolean useHypotheses;

  protected BaseEqualitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr, TypedExpression instance, boolean useHypotheses) {
    this.meta = meta;
    this.typechecker = typechecker;
    this.factory = factory;
    this.refExpr = refExpr;
    this.instance = instance;
    dataRef = factory.local("d");
    values = new Values<>(typechecker, refExpr);
    this.useHypotheses = useHypotheses;
  }

  protected BaseEqualitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr, TypedExpression instance) {
    this(meta, typechecker, factory, refExpr, instance, true);
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

  /*
  @Override
  public void useDataFromOtherSolver(@NotNull EquationSolver solver) {
    if (solver instanceof BaseEqualitySolver) {

    }
  } /**/

  @Override
  public SubexprOccurrences matchSubexpr(@NotNull TypedExpression subExpr, @NotNull TypedExpression expr, @NotNull ErrorReporter errorReporter, List<Integer> occurrences) {
    var eqProof = solve(null, expr, subExpr, errorReporter);
    var occurrence = occurrences == null ? 0 : occurrences.get(0);

    if (occurrence != 0 || eqProof == null) {
      return new SubexprOccurrences(null, null, null, 0, eqProof == null ? 0 : 1);
    }

    return SubexprOccurrences.simpleSingletonOccur(factory, subExpr.getType(), eqProof);
  }

  public void setUseHypotheses(boolean useHypotheses) {
    this.useHypotheses = useHypotheses;
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    return typechecker.typecheck(result, null);
  }
}
