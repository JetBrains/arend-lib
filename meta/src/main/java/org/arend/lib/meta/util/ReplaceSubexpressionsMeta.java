package org.arend.lib.meta.util;

import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreReferenceExpression;
import org.arend.ext.core.expr.UncheckedExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.error.TypeError;
import org.arend.lib.util.Pair;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class ReplaceSubexpressionsMeta implements MetaDefinition {
  private final CoreExpression expression;
  private final List<Pair<CoreExpression,ArendRef>> substPairs;

  public ReplaceSubexpressionsMeta(CoreExpression expression, List<Pair<CoreExpression,ArendRef>> substPairs) {
    this.expression = expression;
    this.substPairs = substPairs;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    UncheckedExpression result = Utils.tryTypecheck(typechecker, tc -> expression.replaceSubexpressions(expr -> {
      for (Pair<CoreExpression, ArendRef> pair : substPairs) {
        boolean ok = false;
        if (pair.proj1 instanceof CoreReferenceExpression) {
          if (expr instanceof CoreReferenceExpression && ((CoreReferenceExpression) pair.proj1).getBinding() == ((CoreReferenceExpression) expr).getBinding()) {
            ok = true;
          }
        } else {
          if (tc.compare(expr, pair.proj1, CMP.EQ, contextData.getMarker(), false, true)) {
            tc.updateSavedState();
            ok = true;
          } else {
            tc.loadSavedState();
          }
        }
        if (ok) {
          CoreBinding binding = tc.getFreeBinding(pair.proj2);
          return binding == null ? null : binding.makeReference();
        }
      }
      return null;
    }));
    if (result == null) {
      typechecker.getErrorReporter().report(new TypeError("Cannot substitute expressions", expression, contextData.getMarker()));
      return null;
    }
    return typechecker.check(result, contextData.getMarker());
  }
}
