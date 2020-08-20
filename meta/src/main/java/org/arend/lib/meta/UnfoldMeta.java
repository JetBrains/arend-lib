package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.IgnoredArgumentError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class UnfoldMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public UnfoldMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { true, true };
  }

  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return arguments.get(1).getExpression();
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteExpression> firstArgList = Utils.getArgumentList(contextData.getArguments().get(0).getExpression());
    Set<CoreFunctionDefinition> functions = new HashSet<>();
    for (ConcreteExpression expr : firstArgList) {
      CoreFunctionDefinition function = null;
      if (expr instanceof ConcreteReferenceExpression) {
        CoreDefinition def = ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) expr).getReferent());
        if (def instanceof CoreFunctionDefinition) {
          function = (CoreFunctionDefinition) def;
        }
      }
      if (function != null && function.getBody() instanceof CoreExpression) {
        if (!functions.add(function)) {
          typechecker.getErrorReporter().report(new IgnoredArgumentError("Repeated function", expr));
        }
      } else {
        typechecker.getErrorReporter().report(new TypecheckingError(function == null ? "Expected a function" : "Function '" + function.getName() + "' cannot be unfolded", expr));
      }
    }

    Set<CoreFunctionDefinition> unfolded = new HashSet<>();
    TypedExpression result;
    if (contextData.getExpectedType() != null) {
      result = typechecker.typecheck(contextData.getArguments().get(1).getExpression(), contextData.getExpectedType().unfold(functions, unfolded));
    } else {
      TypedExpression arg = typechecker.typecheck(contextData.getArguments().get(1).getExpression(), null);
      if (arg == null) {
        return null;
      }
      result = arg.replaceType(arg.getType().unfold(functions, unfolded));
    }

    if (unfolded.size() != functions.size()) {
      for (ConcreteExpression expr : firstArgList) {
        if (expr instanceof ConcreteReferenceExpression) {
          CoreDefinition def = ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) expr).getReferent());
          if (def instanceof CoreFunctionDefinition && !unfolded.contains(def)) {
            typechecker.getErrorReporter().report(new IgnoredArgumentError("Function was not unfolded", expr));
            unfolded.add((CoreFunctionDefinition) def);
          }
        }
      }
    }

    return result;
  }
}
