package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class UnfoldsMeta extends BaseMetaDefinition {
  @Override
  public boolean[] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return arguments.get(0).getExpression();
  }

  private CoreExpression unfold(CoreExpression expr) {
    while (true) {
      expr = expr.normalize(NormalizationMode.WHNF);
      if (expr instanceof CoreFunCallExpression && ((CoreFunCallExpression) expr).getDefinition().getActualBody() instanceof CoreExpression) {
        CoreExpression newExpr = ((CoreFunCallExpression) expr).evaluate();
        if (newExpr != null) {
          expr = newExpr;
          continue;
        }
      }
      break;
    }
    return expr;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    if (contextData.getExpectedType() != null) {
      return typechecker.typecheck(contextData.getArguments().get(contextData.getArguments().size() - 1).getExpression(), unfold(contextData.getExpectedType()));
    } else {
      TypedExpression arg = typechecker.typecheck(contextData.getArguments().get(contextData.getArguments().size() - 1).getExpression(), null);
      return arg == null ? null : typechecker.replaceType(arg, unfold(arg.getType()), contextData.getMarker(), true);
    }
  }
}
