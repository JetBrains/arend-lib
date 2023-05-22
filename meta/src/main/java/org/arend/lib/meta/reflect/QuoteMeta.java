package org.arend.lib.meta.reflect;

import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class QuoteMeta implements MetaDefinition {
  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    typechecker.getErrorReporter().report(new TypecheckingError("This meta is allowed only under 'reflect' meta", contextData.getMarker()));
    return null;
  }
}
