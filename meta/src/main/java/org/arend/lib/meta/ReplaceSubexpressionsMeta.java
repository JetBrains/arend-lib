package org.arend.lib.meta;

import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.UncheckedExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.util.Pair;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

class ReplaceSubexpressionsMeta implements MetaDefinition {
  private final CoreExpression expression;
  private final List<Pair<CoreExpression,ArendRef>> substPairs;

  public ReplaceSubexpressionsMeta(CoreExpression expression, List<Pair<CoreExpression,ArendRef>> substPairs) {
    this.expression = expression;
    this.substPairs = substPairs;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    UncheckedExpression result = typechecker.withCurrentState(tc -> expression.replaceSubexpressions(expr -> {
      for (Pair<CoreExpression, ArendRef> pair : substPairs) {
        if (tc.compare(expr, pair.proj1, CMP.EQ, contextData.getMarker(), false, true)) {
          tc.updateSavedState();
          CoreBinding binding = tc.getFreeBinding(pair.proj2);
          return binding == null ? null : binding.makeReference();
        }
        tc.loadSavedState();
      }
      return null;
    }));
    if (result == null) {
      typechecker.getErrorReporter().report(new TypecheckingError("Cannot substitute expressions", contextData.getMarker()));
      return null;
    }
    return typechecker.check(result, contextData.getMarker());
  }
}
