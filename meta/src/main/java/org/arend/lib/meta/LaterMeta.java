package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.MetaRef;
import org.arend.ext.typechecking.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class LaterMeta extends BaseMetaDefinition {
  @Override
  protected @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  protected boolean requireExpectedType() {
    return true;
  }

  @Override
  protected boolean allowExcessiveArguments() {
    return true;
  }

  @Override
  public @Nullable CheckedExpression invoke(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    MetaDefinition meta = null;
    List<? extends ConcreteArgument> args = contextData.getArguments();
    ConcreteExpression arg = args.get(0).getExpression();
    if (arg instanceof ConcreteReferenceExpression) {
      ArendRef ref = ((ConcreteReferenceExpression) arg).getReferent();
      if (ref instanceof MetaRef) {
        meta = ((MetaRef) ref).getDefinition();
      }
    }
    if (meta == null) {
      typechecker.getErrorReporter().report(new TypecheckingError("Expected a meta definition", arg));
      return null;
    }

    contextData.setArguments(args.subList(1, args.size()));
    return typechecker.defer(meta, contextData, contextData.getCheckedExpectedType(), ExpressionTypechecker.Stage.BEFORE_SOLVER);
  }
}
