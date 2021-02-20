package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.ops.NormalizationMode;
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
  public boolean[] argumentExplicitness() {
    return new boolean[] { true, true };
  }

  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  @Override
  public int @Nullable [] desugarArguments(@NotNull List<? extends ConcreteArgument> arguments) {
    if (arguments.isEmpty()) return null;
    int[] result = new int[arguments.size() - 1];
    for (int i = 0; i < result.length; i++) {
      result[i] = i + 1;
    }
    return result;
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return arguments.get(1).getExpression();
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteExpression> firstArgList = Utils.getArgumentList(contextData.getArguments().get(0).getExpression());
    Set<CoreDefinition> functions = new HashSet<>();
    for (ConcreteExpression expr : firstArgList) {
      CoreDefinition function = null;
      if (expr instanceof ConcreteReferenceExpression) {
        CoreDefinition def = ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) expr).getReferent());
        if (def instanceof CoreFunctionDefinition || def instanceof CoreClassField) {
          function = def;
        }
      }
      if (function == null || function instanceof CoreFunctionDefinition && !(((CoreFunctionDefinition) function).getBody() instanceof CoreExpression) || function instanceof CoreClassField && ((CoreClassField) function).isProperty()) {
        typechecker.getErrorReporter().report(new TypecheckingError(function == null ? "Expected either a function or a field" : "Function '" + function.getName() + "' cannot be unfolded", expr));
      } else {
        if (!functions.add(function)) {
          typechecker.getErrorReporter().report(new IgnoredArgumentError("Repeated function", expr));
        }
      }
    }

    Set<CoreDefinition> unfolded = new HashSet<>();
    TypedExpression result;
    if (contextData.getExpectedType() != null) {
      result = typechecker.typecheck(contextData.getArguments().get(1).getExpression(), contextData.getExpectedType().normalize(NormalizationMode.RNF).unfold(functions, unfolded, false));
    } else {
      TypedExpression arg = typechecker.typecheck(contextData.getArguments().get(1).getExpression(), null);
      if (arg == null) {
        return null;
      }
      result = arg.replaceType(arg.getType().unfold(functions, unfolded, false));
    }

    if (unfolded.size() != functions.size()) {
      for (ConcreteExpression expr : firstArgList) {
        if (expr instanceof ConcreteReferenceExpression) {
          CoreDefinition def = ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) expr).getReferent());
          if ((def instanceof CoreFunctionDefinition || def instanceof CoreClassField) && !unfolded.contains(def)) {
            typechecker.getErrorReporter().report(new IgnoredArgumentError("Function was not unfolded", expr));
            unfolded.add(def);
          }
        }
      }
    }

    return result;
  }
}
