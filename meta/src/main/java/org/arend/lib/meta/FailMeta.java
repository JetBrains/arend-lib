package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class FailMeta extends MetaInvocationMeta {
  private final StdExtension ext;

  public FailMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false, true };
  }

  private ConcreteExpression makeResult(Object data) {
    return ext.factory.withData(data).tuple();
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return makeResult(null);
  }

  @Override
  public TypedExpression invokeMeta(MetaDefinition meta, List<ConcreteExpression> implicitArgs, ExpressionTypechecker typechecker, ContextData contextData) {
    CoreExpression originalExpectedType = contextData.getExpectedType();
    if (!implicitArgs.isEmpty()) {
      TypedExpression type = typechecker.typecheck(implicitArgs.get(0), null);
      if (type == null) {
        return null;
      }
      contextData.setExpectedType(type.getExpression());
    }

    TypedExpression result = Utils.tryTypecheck(typechecker, tc -> meta.checkAndInvokeMeta(tc, contextData));
    if (result == null) {
      return typechecker.typecheck(makeResult(contextData.getReferenceExpression().getData()), originalExpectedType);
    }

    typechecker.getErrorReporter().report(new TypecheckingError("Meta did not fail", contextData.getReferenceExpression()));
    return null;
  }
}
