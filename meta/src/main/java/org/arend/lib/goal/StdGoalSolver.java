package org.arend.lib.goal;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.expr.*;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.GeneralError;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

public class StdGoalSolver implements GoalSolver {
  private final StdExtension ext;

  public StdGoalSolver(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @NotNull CheckGoalResult checkGoal(@NotNull ExpressionTypechecker typechecker, @NotNull ConcreteGoalExpression goalExpression, @Nullable CoreExpression expectedType) {
    ConcreteExpression expr = goalExpression.getExpression();
    if (expr == null) {
      return new CheckGoalResult(null, null);
    }

    if (expectedType == null || !(expr instanceof ConcreteReferenceExpression || expr instanceof ConcreteAppExpression)) {
      return new CheckGoalResult(goalExpression.getOriginalExpression(), typechecker.typecheck(expr, expectedType));
    }

    int expectedParams = Utils.numberOfExplicitPiParameters(expectedType);

    Object exprData = expr.getData();
    ConcreteFactory factory = ext.factory.withData(exprData);
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    List<ConcreteExpression> args = Utils.addArguments(expr, ext, expectedParams, true);
    ConcreteExpression extExpr = args.isEmpty() ? expr : factory.app(expr, true, args);
    TypedExpression result = typechecker.withErrorReporter(error -> {
      if (!(error.level == GeneralError.Level.GOAL && error.getCause() == exprData)) {
        errorReporter.report(error);
      }
    }, tc -> tc.typecheck(extExpr, expectedType));

    ConcreteExpression cExpr = goalExpression.getOriginalExpression();
    if (cExpr != null) {
      cExpr = args.isEmpty() ? cExpr : factory.app(cExpr, true, args);
    }
    return new CheckGoalResult(result == null || cExpr == null ? cExpr : Utils.addArguments(cExpr, factory, Utils.numberOfExplicitPiParameters(result.getType()) - expectedParams, true), result);
  }

  @Override
  public @NotNull Collection<? extends InteractiveGoalSolver> getAdditionalSolvers() {
    return Collections.singletonList(new ConstructorGoalSolver(ext));
  }
}
