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
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  @Override
  public boolean allowExcessiveArguments() {
    return true;
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    ConcreteExpression expr = arguments.get(0).getExpression();
    if (expr instanceof ConcreteReferenceExpression) {
      ArendRef ref = ((ConcreteReferenceExpression) expr).getReferent();
      if (ref instanceof MetaRef) {
        MetaDefinition def = ((MetaRef) ref).getDefinition();
        if (def != null) {
          return def.checkAndGetConcreteRepresentation(arguments.subList(1, arguments.size()));
        }
      }
    }
    return null;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
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
    return typechecker.defer(meta, contextData, contextData.getExpectedType());
  }
}
