package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteTupleExpression;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

public class InMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public InMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean[] argumentExplicitness() {
    return new boolean[] { true, true };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    List<? extends ConcreteArgument> args = contextData.getArguments();
    ConcreteExpression arg = args.get(0).getExpression();
    if (arg instanceof ConcreteTupleExpression tuple && tuple.getFields().size() != 1) {
      var fields = tuple.getFields();
      if (fields.isEmpty()) {
        return typechecker.typecheck(factory.app(args.get(1).getExpression(), args.subList(2, args.size())), null);
      }
      List<ConcreteArgument> newArgs = new ArrayList<>(args);
      newArgs.set(0, factory.arg(fields.get(0), true));
      ConcreteExpression result = factory.app(contextData.getReferenceExpression(), newArgs);
      for (int i = 1; i < fields.size() - 1; i++) {
        result = factory.app(contextData.getReferenceExpression(), true, fields.get(i), result);
      }
      return typechecker.typecheck(factory.app(contextData.getReferenceExpression(), true, fields.get(fields.size() - 1), result), null);
    } else {
      return typechecker.typecheck(factory.app(arg, args.subList(1, args.size())), null);
    }
  }
}
