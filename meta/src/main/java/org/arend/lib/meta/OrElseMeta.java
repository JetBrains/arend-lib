package org.arend.lib.meta;

import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class OrElseMeta extends BaseMetaDefinition {
  @Override
  public boolean[] argumentExplicitness() {
    return new boolean[] { true, true };
  }

  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(contextData.getArguments().get(0).getExpression(), contextData.getExpectedType()));
    return result != null ? result : typechecker.typecheck(contextData.getArguments().get(1).getExpression(), contextData.getExpectedType());
  }
}
