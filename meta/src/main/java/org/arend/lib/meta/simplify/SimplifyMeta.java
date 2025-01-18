package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.core.expr.*;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class SimplifyMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public SimplifyMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }



  @Override
  public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    var refExpr = contextData.getReferenceExpression();
    boolean isForward = contextData.getExpectedType() == null;
    CoreExpression expectedType = contextData.getExpectedType();
    List<? extends ConcreteArgument> args = contextData.getArguments();

    if (isForward && args.isEmpty()) {
      return null;
    }

    var factory = ext.factory.withData(refExpr.getData());
    var expression = args.isEmpty() ? factory.ref(ext.prelude.getIdpRef()) : args.get(0).getExpression();
    CoreExpression type;

    if (isForward) {
      var checkedExpr = typechecker.typecheck(expression, null);
      type = checkedExpr == null ? null : checkedExpr.getType();
    } else {
      type = expectedType == null ? null : expectedType.getUnderlyingExpression();
    }

    if (type == null) {
      return Utils.typecheckWithAdditionalArguments(expression, typechecker, ext, 0, false);
    }

    var transportedExpr = new Simplifier(ext, typechecker, refExpr, factory, typechecker.getErrorReporter()).simplifyTypeOfExpression(expression, type, isForward);
    return transportedExpr == null ? null : typechecker.typecheck(transportedExpr, expectedType);
  }
}
