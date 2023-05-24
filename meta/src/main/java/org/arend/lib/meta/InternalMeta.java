package org.arend.lib.meta;

import org.arend.ext.reference.MetaRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.error.InternalMetaError;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class InternalMeta implements MetaDefinition {
  private final MetaRef externalMeta;

  public InternalMeta(MetaRef externalMeta) {
    this.externalMeta = externalMeta;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    typechecker.getErrorReporter().report(new InternalMetaError(externalMeta, contextData.getMarker()));
    return null;
  }
}
