package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

public class ApplyMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public ApplyMeta(StdExtension ext) {
    this.ext = ext;
  }

  private ConcreteExpression make(List<? extends ConcreteArgument> arguments, ConcreteFactory factory) {
    int i = 0;
    while (i < arguments.size() && !arguments.get(i).isExplicit()) {
      i++;
    }
    if (i == arguments.size()) {
      return null;
    }

    List<ConcreteArgument> args = new ArrayList<>(arguments.size() - 1);
    args.addAll(arguments.subList(0, i));
    args.addAll(arguments.subList(i + 1, arguments.size()));
    return factory.app(arguments.get(i).getExpression(), args);
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return make(arguments, ext.factory);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteExpression result = make(contextData.getArguments(), ext.factory.withData(contextData.getReferenceExpression().getData()));
    if (result == null) {
      typechecker.getErrorReporter().report(new TypecheckingError("Required at least one explicit argument", contextData.getReferenceExpression()));
      return null;
    }
    return typechecker.typecheck(result, contextData.getExpectedType());
  }
}
