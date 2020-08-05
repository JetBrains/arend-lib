package org.arend.lib.meta.debug;

import org.arend.ext.concrete.expr.ConcreteStringExpression;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.ui.ArendConsole;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class PrintMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public PrintMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { true, true };
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }

  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ArendConsole console = ext.ui.getConsole(contextData.getMarker());
    if (contextData.getArguments().get(0).getExpression() instanceof ConcreteStringExpression) {
      console.println(((ConcreteStringExpression) contextData.getArguments().get(0).getExpression()).getUnescapedString());
    } else {
      TypedExpression result = typechecker.typecheck(contextData.getArguments().get(0).getExpression(), null);
      if (result == null) {
        return null;
      }
      console.println(result.getExpression());
    }
    return typechecker.typecheck(contextData.getArguments().size() > 1 ? contextData.getArguments().get(1).getExpression() : ext.factory.withData(contextData.getMarker().getData()).tuple(), contextData.getExpectedType());
  }
}
