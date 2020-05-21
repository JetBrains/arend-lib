package org.arend.lib.meta;

import org.arend.ext.FreeBindingsModifier;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

public class HidingMeta extends BaseMetaDefinition {
  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { true, true };
  }

  public static <T> T invokeMeta(ConcreteExpression argument, ExpressionTypechecker typechecker, Function<ExpressionTypechecker, T> action) {
    Set<CoreBinding> bindings = new HashSet<>();
    for (ConcreteExpression arg : Utils.getArgumentList(argument)) {
      if (arg instanceof ConcreteReferenceExpression) {
        CoreBinding binding = typechecker.getFreeBinding(((ConcreteReferenceExpression) arg).getReferent());
        if (binding != null) {
          bindings.add(binding);
          continue;
        }
      }
      typechecker.getErrorReporter().report(new TypecheckingError("Expected a local variable", arg));
    }
    return typechecker.withFreeBindings(new FreeBindingsModifier().remove(bindings), action);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    return invokeMeta(contextData.getArguments().get(0).getExpression(), typechecker, tc -> tc.typecheck(contextData.getArguments().get(1).getExpression(), contextData.getExpectedType()));
  }
}
