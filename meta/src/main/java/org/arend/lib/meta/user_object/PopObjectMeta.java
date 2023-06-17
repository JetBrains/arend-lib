package org.arend.lib.meta.user_object;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class PopObjectMeta extends BaseObjectMeta {
  private final StdExtension ext;
  private final boolean onlyPeek;

  public PopObjectMeta(StdExtension ext, boolean onlyPeek) {
    this.ext = ext;
    this.onlyPeek = onlyPeek;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true, true, true };
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 2;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    var args = contextData.getArguments();
    UserObjectKey key = getUserObject(args, typechecker.getErrorReporter());
    String defaultMessage = "Cannot " + (onlyPeek ? "peek" : "pop") + " object; the stack is empty";
    String message = args.size() < 3 ? defaultMessage : getMessage(args.get(1).getExpression(), typechecker);
    if (key == null || message == null) return null;
    if (message.isEmpty()) message = defaultMessage;
    List<ConcreteExpression> stack = typechecker.getUserData(key);
    if (stack == null || stack.isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(message, contextData.getMarker()));
      return null;
    }
    ConcreteExpression object = stack.get(stack.size() - 1);
    if (!onlyPeek) {
      stack.remove(stack.size() - 1);
    }
    return typechecker.typecheck(args.size() <= 1 ? object : Utils.applyExpression(args.get(args.size() - 1).getExpression(), object, ext.factory.withData(contextData.getMarker())), contextData.getExpectedType());
  }
}
