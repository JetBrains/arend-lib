package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteAppBuilder;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class MakeConstructorMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public MakeConstructorMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean[] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteExpression arg = contextData.getArguments().get(0).getExpression();
    CoreConstructor constructor = null;
    if (arg instanceof ConcreteReferenceExpression) {
      CoreDefinition def = ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) arg).getReferent());
      if (def instanceof CoreConstructor) constructor = (CoreConstructor) def;
    }
    if (constructor == null) {
      typechecker.getErrorReporter().report(new TypecheckingError("Expected a constructor", arg));
      return null;
    }

    int dataTypeParams = Utils.parametersSize(constructor.getDataTypeParameters());
    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    ConcreteAppBuilder builder = factory.appBuilder(arg);
    for (int i = 0; i < dataTypeParams; i++) {
      builder.app(factory.hole(), false);
    }
    for (int i = 1; i < contextData.getArguments().size(); i++) {
      builder.app(contextData.getArguments().get(i));
    }
    return typechecker.typecheck(builder.build(), contextData.getExpectedType());
  }
}
