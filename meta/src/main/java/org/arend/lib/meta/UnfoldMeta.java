package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteAppExpression;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreEvaluatingBinding;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.quickFix.RemoveErrorQuickFix;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.variable.Variable;
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
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }

  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  @Override
  public int @Nullable [] desugarArguments(@NotNull List<? extends ConcreteArgument> arguments) {
    if (arguments.size() <= 1) return null;
    int[] result = new int[arguments.size() - 1];
    for (int i = 0; i < result.length; i++) {
      result[i] = i + 1;
    }
    return result;
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return arguments.size() > 1 ? arguments.get(1).getExpression() : arguments.get(0).getExpression();
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    Set<Variable> functions = new HashSet<>();
    List<? extends ConcreteExpression> firstArgList;
    boolean unfoldFields = contextData.getArguments().size() == 1;
    if (contextData.getArguments().size() == 2) {
      firstArgList = Utils.getArgumentList(contextData.getArguments().get(0).getExpression());
      for (ConcreteExpression expr : firstArgList) {
        Variable var = null;
        while (expr instanceof ConcreteAppExpression) {
          expr = ((ConcreteAppExpression) expr).getFunction();
        }
        if (expr instanceof ConcreteReferenceExpression) {
          CoreDefinition def = ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) expr).getReferent());
          if (def instanceof CoreFunctionDefinition || def instanceof CoreClassField) {
            var = def;
          }
          if (def == null) {
            CoreBinding binding = typechecker.getFreeBinding(((ConcreteReferenceExpression) expr).getReferent());
            if (binding instanceof CoreEvaluatingBinding) {
              var = binding;
            }
          }
        }
        if (var == null || var instanceof CoreFunctionDefinition && !(((CoreFunctionDefinition) var).getBody() instanceof CoreExpression) && ((CoreFunctionDefinition) var).getKind() != CoreFunctionDefinition.Kind.TYPE || var instanceof CoreClassField && ((CoreClassField) var).isProperty()) {
          typechecker.getErrorReporter().report(new TypecheckingError(var == null ? "Expected either a function or a field" : "Function '" + var.getName() + "' cannot be unfolded", expr).withQuickFix(new RemoveErrorQuickFix("Remove")));
        } else {
          if (!functions.add(var)) {
            typechecker.getErrorReporter().report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Repeated function", expr).withQuickFix(new RemoveErrorQuickFix("Remove function")));
          }
        }
      }
    } else {
      firstArgList = null;
    }

    Set<Variable> unfolded = new HashSet<>();
    TypedExpression result;
    if (contextData.getExpectedType() != null) {
      result = typechecker.typecheck(contextData.getArguments().get(contextData.getArguments().size() - 1).getExpression(), contextData.getExpectedType().normalize(NormalizationMode.RNF).unfold(functions, unfolded, false, unfoldFields));
    } else {
      TypedExpression arg = typechecker.typecheck(contextData.getArguments().get(contextData.getArguments().size() - 1).getExpression(), null);
      if (arg == null) {
        return null;
      }
      result = typechecker.replaceType(arg, arg.getType().normalize(NormalizationMode.RNF).unfold(functions, unfolded, false, unfoldFields), contextData.getMarker(), false);
    }

    if (firstArgList != null && unfolded.size() != functions.size()) {
      for (ConcreteExpression expr : firstArgList) {
        if (expr instanceof ConcreteReferenceExpression) {
          CoreDefinition def = ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) expr).getReferent());
          if ((def instanceof CoreFunctionDefinition || def instanceof CoreClassField) && !unfolded.contains(def)) {
            typechecker.getErrorReporter().report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Function was not unfolded", expr).withQuickFix(new RemoveErrorQuickFix("Remove function")));
            unfolded.add(def);
          }
          if (def == null) {
            CoreBinding binding = typechecker.getFreeBinding(((ConcreteReferenceExpression) expr).getReferent());
            if (binding instanceof CoreEvaluatingBinding && !unfolded.contains(binding)) {
              typechecker.getErrorReporter().report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Binding was not unfolded", expr).withQuickFix(new RemoveErrorQuickFix("Remove binding")));
              unfolded.add(binding);
            }
          }
        }
      }
    }

    return result;
  }
}
