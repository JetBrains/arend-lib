package org.arend.lib.meta.debug;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class SleepMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public SleepMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean[] argumentExplicitness() {
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
    List<? extends ConcreteArgument> args = contextData.getArguments();
    int millis = Utils.getNumber(args.get(0).getExpression(), typechecker.getErrorReporter());
    if (millis < 0) return null;

    try {
      Thread.sleep(millis);
    } catch (InterruptedException e) {
      return null;
    }

    return typechecker.typecheck(args.size() > 1 ? args.get(1).getExpression() : ext.factory.withData(contextData.getMarker().getData()).tuple(), contextData.getExpectedType());
  }
}
