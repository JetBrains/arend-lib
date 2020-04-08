package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class ApplyMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public ApplyMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Nullable
  @Override
  protected boolean[] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return ext.factory.app(arguments.get(0).getExpression(), arguments.subList(1, arguments.size()));
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    return typechecker.typecheck(ext.factory.withData(contextData.getReferenceExpression().getData()).app(args.get(0).getExpression(), args.subList(1, args.size())), contextData.getExpectedType());
  }
}
