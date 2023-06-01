package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class ReflectMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public ReflectMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteExpression arg = contextData.getArguments().get(0).getExpression();
    ConcreteExpression result;
    try {
      result = arg.accept(new ReflectBuilder(typechecker, ext, ext.factory.withData(contextData.getMarker())), null);
    } catch (ReflectionException e) {
      typechecker.getErrorReporter().report(e.error);
      return null;
    }
    TypedExpression typed = typechecker.typecheck(result, contextData.getExpectedType());
    return typed == null ? null : typed.makeDataExpression(new ReflectedExpression(arg));
  }
}
