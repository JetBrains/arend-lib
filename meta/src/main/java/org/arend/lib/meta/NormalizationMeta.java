package org.arend.lib.meta;

import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class NormalizationMeta extends BaseMetaDefinition {
  private final NormalizationMode mode;

  public NormalizationMeta(NormalizationMode mode) {
    this.mode = mode;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    TypedExpression result = typechecker.typecheck(contextData.getArguments().get(0).getExpression(), contextData.getExpectedType());
    return result == null ? null : result.getExpression().normalize(mode).computeTyped();
  }
}
