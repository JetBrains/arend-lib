package org.arend.lib.meta.user_object;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

public class PushObjectMeta extends BaseObjectMeta {
  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true, true, true };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    var args = contextData.getArguments();
    UserObjectKey key = getUserObject(args, typechecker.getErrorReporter());
    if (key == null) return null;
    List<ConcreteExpression> stack = typechecker.getUserData(key);
    if (stack == null) {
      stack = new ArrayList<>();
      typechecker.putUserData(key, stack);
    }
    stack.add(args.get(1).getExpression());
    return typechecker.typecheck(args.get(2).getExpression(), contextData.getExpectedType());
  }
}
