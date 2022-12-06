package org.arend.lib.meta;

import org.arend.ext.FreeBindingsModifier;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;

public class UsingMeta extends BaseMetaDefinition {
  public final boolean keepOldContext;

  public UsingMeta(boolean keepOldContext) {
    this.keepOldContext = keepOldContext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { true, true };
  }

  private static void getNewBindings(ConcreteExpression argument, ExpressionTypechecker typechecker, List<CoreBinding> newBindings, Collection<CoreBinding> retainSet, boolean keepOldContext) {
    for (ConcreteExpression arg : Utils.getArgumentList(argument)) {
      if (arg instanceof ConcreteReferenceExpression) {
        CoreBinding binding = typechecker.getFreeBinding(((ConcreteReferenceExpression) arg).getReferent());
        if (binding != null) {
          if (keepOldContext) {
            typechecker.getErrorReporter().report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Variable is already in the context", arg));
          } else {
            retainSet.add(binding);
          }
          continue;
        }
      }

      TypedExpression result = typechecker.typecheck(arg, null);
      if (result != null) {
        newBindings.add(result.makeEvaluatingBinding(null));
      }
    }
  }

  public static List<CoreBinding> getNewBindings(ConcreteExpression argument, ExpressionTypechecker typechecker, boolean keepOldContext) {
    List<CoreBinding> result = new ArrayList<>();
    getNewBindings(argument, typechecker, result, result, keepOldContext);
    return result;
  }

  public <T> T invokeMeta(ConcreteExpression argument, ExpressionTypechecker typechecker, Function<ExpressionTypechecker, T> action) {
    List<CoreBinding> newBindings = new ArrayList<>();
    Set<CoreBinding> retainSet = keepOldContext ? null : new HashSet<>();
    getNewBindings(argument, typechecker, newBindings, retainSet, keepOldContext);

    FreeBindingsModifier modifier = new FreeBindingsModifier();
    if (retainSet != null) {
      modifier.retain(retainSet);
    }
    if (!newBindings.isEmpty()) {
      modifier.add(newBindings);
    }
    return typechecker.withFreeBindings(modifier, action);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    return invokeMeta(contextData.getArguments().get(0).getExpression(), typechecker,
        tc -> tc.typecheck(contextData.getArguments().get(1).getExpression(), contextData.getExpectedType()));
  }
}
