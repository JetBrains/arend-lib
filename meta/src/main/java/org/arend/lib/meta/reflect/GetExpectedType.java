package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class GetExpectedType extends BaseMetaDefinition {
  private final StdExtension ext;

  public GetExpectedType(StdExtension ext) {
    this.ext = ext;
  }

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
    CoreExpression expectedType = contextData.getExpectedType();
    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    ConcreteExpression result;
    if (expectedType == null) {
      result = factory.app(factory.ref(ext.nothing.getRef()), false, factory.ref(ext.tcMeta.ConcreteExpr.getRef()));
    } else {
      ConcreteExpression concreteType = ext.reflectCore(expectedType, typechecker, factory);
      if (concreteType == null) return null;
      result = factory.app(factory.ref(ext.just.getRef()), true, concreteType);
    }
    return typechecker.typecheck(Utils.applyExpression(contextData.getArguments().get(0).getExpression(), result, factory), expectedType);
  }
}
