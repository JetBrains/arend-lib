package org.arend.lib.meta.equation;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.util.Maybe;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public interface EquationSolver {
  boolean isApplicable(CoreExpression type);
  CoreExpression getValuesType(); // the type of left and right hand sides
  CoreExpression getLeftValue();  // the left hand side of the equation
  CoreExpression getRightValue(); // the right hand side of the equation

  @Nullable Maybe<CoreExpression> getEqType(@Nullable TypedExpression leftExpr, @Nullable TypedExpression rightExpr); // the type of equality between two expressions
  TypedExpression getTrivialResult(TypedExpression expression); // reflexivity, trivial path, etc
  ConcreteExpression combineResults(ConcreteExpression expr1, ConcreteExpression expr2); // transitivity, concatenation, etc

  boolean isHint(ConcreteExpression expression);
  boolean initializeSolver();
  ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter);
  TypedExpression finalize(ConcreteExpression result);
}
