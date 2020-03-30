package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.CheckedExpression;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class ApplyMeta extends BaseMetaDefinition {
  @Nullable
  @Override
  protected boolean[] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public @Nullable CheckedExpression invoke(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    return typechecker.typecheck(args.get(0).getExpression().app(args.subList(1, args.size())), contextData.getExpectedType());
  }
}
