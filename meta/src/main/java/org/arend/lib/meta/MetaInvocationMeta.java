package org.arend.lib.meta;

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
  public int getNumberOfImplicitArguments() {
    return 0;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    int implicitArgs = getNumberOfImplicitArguments();
    boolean[] result = new boolean[implicitArgs + 1];
    result[implicitArgs] = true;
    return result;
  }

  @Override
  public boolean allowExcessiveArguments() {
    return true;
  }

  private List<? extends ConcreteArgument> mergeArgs(List<? extends ConcreteArgument> args1, List<? extends ConcreteArgument> args2) {
    int n = 0;
    for (; n < args2.size(); n++) {
      if (args2.get(n).isExplicit()) {
        break;
      }
    }
    // skip implicit arguments and the first explicit, which is the meta reference
    args2 = args2.subList(n + 1, args2.size());

    if (args1 == null) {
      return args2;
    }

    List<ConcreteArgument> totalArgs = new ArrayList<>(args1);
    totalArgs.addAll(args2);
    return totalArgs;
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    ConcreteExpression expr = arguments.get(0).getExpression();
    List<? extends ConcreteArgument> metaArgs = null;
    if (expr instanceof ConcreteAppExpression) {
      expr = ((ConcreteAppExpression) expr).getFunction();
      metaArgs = ((ConcreteAppExpression) expr).getArguments();
    }
    if (expr instanceof ConcreteReferenceExpression) {
      ArendRef ref = ((ConcreteReferenceExpression) expr).getReferent();
      if (ref instanceof MetaRef) {
        MetaDefinition def = ((MetaRef) ref).getDefinition();
        if (def != null) {
          return def.checkAndGetConcreteRepresentation(mergeArgs(metaArgs, arguments));
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
    int numberOfImplicitArgs = getNumberOfImplicitArguments();
    int currentArg = 0;
    for (; currentArg < numberOfImplicitArgs; currentArg++) {
      if (!args.get(currentArg).isExplicit()) {
        implicitArgs.add(args.get(currentArg).getExpression());
      } else {
        break;
      }
    }
    ConcreteExpression arg = args.get(currentArg).getExpression();

    if (arg instanceof ConcreteAppExpression) {
      arg = ((ConcreteAppExpression) arg).getFunction();
      metaArgs = ((ConcreteAppExpression) arg).getArguments();
    }
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

    contextData.setArguments(mergeArgs(metaArgs, args));
    return invokeMeta(meta, implicitArgs, typechecker, contextData);
  }
}
