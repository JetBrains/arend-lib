package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class OrElseMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public OrElseMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean[] argumentExplicitness() {
    return new boolean[] { true, true };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    ConcreteExpression arg1 = args.get(0).getExpression();
    ConcreteExpression arg2 = args.get(1).getExpression();
    if (args.size() > 2) {
      ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
      arg1 = factory.app(arg1, args.subList(2, args.size()));
      arg2 = factory.app(arg2, args.subList(2, args.size()));
    }
    ConcreteExpression finalArg1 = arg1;
    TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(finalArg1, contextData.getExpectedType()));
    return result != null ? result : typechecker.typecheck(arg2, contextData.getExpectedType());
  }
}
