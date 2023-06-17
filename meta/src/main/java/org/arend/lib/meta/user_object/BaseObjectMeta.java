package org.arend.lib.meta.user_object;

import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreQNameExpression;
import org.arend.ext.core.expr.CoreStringExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;

import java.util.List;

public abstract class BaseObjectMeta extends BaseMetaDefinition {
  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  UserObjectKey getUserObject(List<? extends ConcreteArgument> args, ExpressionTypechecker typechecker) {
    if (args.get(0).getExpression() instanceof ConcreteQNameExpression qName) {
      return new UserObjectKey(qName.getReference());
    }

    TypedExpression result = typechecker.typecheck(args.get(0).getExpression(), null);
    if (result == null) return null;
    CoreExpression expr = result.getExpression().normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreQNameExpression qName) {
      return new UserObjectKey(qName.getRef());
    }

    typechecker.getErrorReporter().report(new TypecheckingError("Expected a reference", args.get(0).getExpression()));
    return null;
  }

  String getMessage(ConcreteExpression arg, ExpressionTypechecker typechecker) {
    if (arg instanceof ConcreteStringExpression) {
      return ((ConcreteStringExpression) arg).getUnescapedString();
    }

    TypedExpression result = typechecker.typecheck(arg, null);
    if (result == null) return null;
    CoreExpression expr = result.getExpression().normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreStringExpression) {
      return ((CoreStringExpression) expr).getString();
    }

    typechecker.getErrorReporter().report(new TypecheckingError("Expected a string", arg));
    return null;
  }
}
