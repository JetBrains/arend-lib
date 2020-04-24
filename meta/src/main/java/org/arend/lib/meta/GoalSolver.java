package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteAppExpression;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteGoalExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.GeneralError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

public class GoalSolver extends BaseMetaDefinition {
  private final StdExtension ext;

  public GoalSolver(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteGoalExpression goalExpr = contextData.getGoalExpression();
    ConcreteExpression expr = goalExpr.getExpression();
    if (expr == null) {
      return null;
    }

    CoreExpression expectedType = contextData.getExpectedType();
    if (!(expectedType != null && (expr instanceof ConcreteReferenceExpression || expr instanceof ConcreteAppExpression))) {
      return typechecker.typecheck(expr, expectedType);
    }

    List<CoreParameter> expectedParameters = new ArrayList<>();
    expectedType.getPiParameters(expectedParameters);
    int expectedParams = Utils.numberOfExplicitParameters(expectedParameters);

    Object exprData = expr.getData();
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    boolean[] hasErrors = new boolean[1];
    TypedExpression result = typechecker.withErrorReporter(error -> {
      if (!(error.level == GeneralError.Level.GOAL && error.getCause() == exprData)) {
        if (error.level == GeneralError.Level.ERROR) {
          hasErrors[0] = true;
        }
        errorReporter.report(error);
      }
    }, tc -> Utils.typecheckWithAdditionalArguments(expr, typechecker, ext, expectedParams, true));
    return hasErrors[0] ? null : result;
  }
}
