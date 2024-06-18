package org.arend.lib.meta.util;

import org.arend.ext.concrete.ConcreteSourceNode;
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
import org.arend.ext.util.Pair;
import org.arend.lib.error.TypeError;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class ReplaceSubexpressionsMeta implements MetaDefinition {
  private final CoreExpression expression;
  private final List<Pair<TypedExpression,Object>> substPairs;

  public ReplaceSubexpressionsMeta(CoreExpression expression, List<Pair<TypedExpression,Object>> substPairs) {
    this.expression = expression;
    this.substPairs = substPairs;
  }

  public TypedExpression invoke(@NotNull ExpressionTypechecker typechecker, @NotNull ConcreteSourceNode marker) {
    return Utils.tryTypecheck(typechecker, tc -> {
      UncheckedExpression replaced = expression.replaceSubexpressions(expr -> {
        for (Pair<TypedExpression, Object> pair : substPairs) {
          boolean ok = false;
          if (pair.proj1 instanceof CoreReferenceExpression) {
            if (expr instanceof CoreReferenceExpression && ((CoreReferenceExpression) pair.proj1).getBinding() == ((CoreReferenceExpression) expr).getBinding()) {
              ok = true;
            }
          } else {
            if (tc.compare(pair.proj1.getType(), expr.computeType(), CMP.LE, marker, false, true, false) && tc.compare(expr, pair.proj1.getExpression(), CMP.EQ, marker, false, true, true)) {
              tc.updateSavedState();
              ok = true;
            } else {
              tc.loadSavedState();
            }
          }
          if (ok) {
            CoreBinding binding = pair.proj2 instanceof CoreBinding ? (CoreBinding) pair.proj2 : tc.getFreeBinding((ArendRef) pair.proj2);
            return binding == null ? null : binding.makeReference();
          }
        }
        return null;
      }, false);
      return replaced == null ? null : typechecker.check(replaced, marker);
    });
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    TypedExpression result = invoke(typechecker, contextData.getMarker());
    if (result == null) {
      typechecker.getErrorReporter().report(new TypeError(typechecker.getExpressionPrettifier(), "Cannot substitute expressions", expression, contextData.getMarker()));
    }
    return result;
  }
}
