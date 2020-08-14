package org.arend.lib.meta.debug;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteNumberExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;
import java.util.concurrent.ThreadLocalRandom;

public class RandomMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public RandomMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { true };
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
    int r;
    if (contextData.getArguments().isEmpty()) {
      r = ThreadLocalRandom.current().nextInt();
    } else {
      List<? extends ConcreteExpression> args = Utils.getArgumentList(contextData.getArguments().get(0).getExpression());
      if (args.size() == 1 && args.get(0) instanceof ConcreteNumberExpression) {
        r = ThreadLocalRandom.current().nextInt(((ConcreteNumberExpression) args.get(0)).getNumber().intValue());
      } else if (args.size() == 2 && args.get(0) instanceof ConcreteNumberExpression && args.get(1) instanceof ConcreteNumberExpression) {
        int lower = ((ConcreteNumberExpression) args.get(0)).getNumber().intValue();
        int upper = ((ConcreteNumberExpression) args.get(1)).getNumber().intValue();
        if (lower >= upper) {
          typechecker.getErrorReporter().report(new TypecheckingError("The lower bound must be less than the upper bound", contextData.getArguments().get(0).getExpression()));
          return null;
        }
        r = ThreadLocalRandom.current().nextInt(lower, upper);
      } else {
        typechecker.getErrorReporter().report(new TypecheckingError("Expected either a number or a pair of numbers", contextData.getArguments().get(0).getExpression()));
        return null;
      }
    }
    return typechecker.typecheck(ext.factory.withData(contextData.getMarker().getData()).number(r), contextData.getExpectedType());
  }
}
