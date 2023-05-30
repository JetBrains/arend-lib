package org.arend.lib.meta.reflect;

import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreStringExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class ErrorMeta extends BaseMetaDefinition {
  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    TypedExpression arg = typechecker.typecheck(contextData.getArguments().get(0).getExpression(), null);
    if (arg == null) return null;
    CoreExpression expr = arg.getExpression().normalize(NormalizationMode.WHNF);
    typechecker.getErrorReporter().report(expr instanceof CoreStringExpression ? new TypecheckingError(((CoreStringExpression) expr).getString(), contextData.getMarker()) : new TypecheckingError("Expected a string", contextData.getArguments().get(0).getExpression()));
    return null;
  }
}
