package org.arend.lib.meta.util;

import org.arend.ext.concrete.expr.ConcreteAppExpression;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.MetaRef;
import org.arend.ext.typechecking.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

public abstract class MetaInvocationMeta extends BaseMetaDefinition {
  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public boolean allowExcessiveArguments() {
    return true;
  }

  protected boolean keepMetaArgument() {
    return false;
  }

  protected boolean allowNonMeta() {
    return true;
  }

  private List<? extends ConcreteArgument> mergeArgs(List<? extends ConcreteArgument> args1, List<? extends ConcreteArgument> args2, int currentArg) {
    if (keepMetaArgument()) {
      return args2.subList(currentArg, args2.size());
    }

    // skip implicit arguments and the first explicit, which is the meta reference
    args2 = args2.subList(currentArg + 1, args2.size());
    if (args1 == null) {
      return args2;
    }

    List<ConcreteArgument> totalArgs = new ArrayList<>(args1);
    totalArgs.addAll(args2);
    return totalArgs;
  }

  private int getImplicitArguments(List<? extends ConcreteArgument> args, List<ConcreteExpression> result) {
    int currentArg = 0;
    for (; currentArg < args.size(); currentArg++) {
      if (!args.get(currentArg).isExplicit()) {
        result.add(args.get(currentArg).getExpression());
      } else {
        break;
      }
    }
    return currentArg;
  }

  public ConcreteExpression getConcreteRepresentation(MetaDefinition meta, List<ConcreteExpression> implicitArguments, @NotNull List<? extends ConcreteArgument> arguments) {
    return meta.checkAndGetConcreteRepresentation(arguments);
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    List<ConcreteExpression> implicitArgs = new ArrayList<>();
    int currentArg = getImplicitArguments(arguments, implicitArgs);

    ConcreteExpression expr = arguments.get(currentArg).getExpression();
    List<? extends ConcreteArgument> metaArgs = null;
    if (expr instanceof ConcreteAppExpression) {
      metaArgs = ((ConcreteAppExpression) expr).getArguments();
      expr = ((ConcreteAppExpression) expr).getFunction();
    }
    if (expr instanceof ConcreteReferenceExpression) {
      ArendRef ref = ((ConcreteReferenceExpression) expr).getReferent();
      if (ref instanceof MetaRef) {
        MetaDefinition def = ((MetaRef) ref).getDefinition();
        if (def != null) {
          return getConcreteRepresentation(def, implicitArgs, mergeArgs(metaArgs, arguments, currentArg));
        }
      }
    }
    return null;
  }

  public abstract TypedExpression invokeMeta(MetaDefinition meta, List<ConcreteExpression> implicitArguments, ExpressionTypechecker typechecker, ContextData contextData);

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    MetaDefinition meta = null;
    List<? extends ConcreteArgument> metaArgs = null;
    List<? extends ConcreteArgument> args = contextData.getArguments();
    List<ConcreteExpression> implicitArgs = new ArrayList<>();
    int currentArg = getImplicitArguments(args, implicitArgs);
    ConcreteExpression arg = args.get(currentArg).getExpression();

    if (arg instanceof ConcreteAppExpression) {
      metaArgs = ((ConcreteAppExpression) arg).getArguments();
      arg = ((ConcreteAppExpression) arg).getFunction();
    }
    if (arg instanceof ConcreteReferenceExpression) {
      ArendRef ref = ((ConcreteReferenceExpression) arg).getReferent();
      if (ref instanceof MetaRef) {
        meta = ((MetaRef) ref).getDefinition();
      }
    }
    if (meta == null) {
      if (allowNonMeta()) {
        return invokeMeta(new MetaDefinition() {
          @Override
          public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
            return typechecker.typecheck(args.get(currentArg).getExpression(), contextData.getExpectedType());
          }
        }, implicitArgs, typechecker, contextData);
      } else {
        typechecker.getErrorReporter().report(new TypecheckingError("Expected a meta definition", arg));
        return null;
      }
    }

    if (!keepMetaArgument()) {
      contextData.setMarker(arg);
    }
    contextData.setArguments(mergeArgs(metaArgs, args, currentArg));
    return invokeMeta(meta, implicitArgs, typechecker, contextData);
  }
}
