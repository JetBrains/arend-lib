package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;
import java.util.List;

public class RunMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public RunMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false };
  }

  private ConcreteExpression getConcreteRepresentation(List<? extends ConcreteArgument> arguments, ErrorReporter errorReporter, ConcreteSourceNode marker) {
    List<? extends ConcreteExpression> args = arguments.isEmpty() ? Collections.emptyList() : Utils.getArgumentList(arguments.get(0).getExpression());
    if (args.isEmpty()) {
      if (errorReporter != null) {
        errorReporter.report(new TypecheckingError("Expected an implicit argument", marker));
      }
      return null;
    }

    ConcreteFactory factory = ext.factory.withData(marker);
    ConcreteExpression result = args.get(args.size() - 1);
    for (int i = args.size() - 2; i >= 0; i--) {
      result = factory.app(args.get(i), true, Collections.singletonList(result));
    }
    return result;
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return getConcreteRepresentation(arguments, null, null);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteExpression result = getConcreteRepresentation(contextData.getArguments(), typechecker.getErrorReporter(), contextData.getMarker());
    return result == null ? null : typechecker.typecheck(result, contextData.getExpectedType());
  }
}
