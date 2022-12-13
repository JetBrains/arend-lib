package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteNumberExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.error.IgnoredArgumentError;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.math.BigInteger;
import java.util.List;

public class AssumptionMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public AssumptionMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { false };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteSourceNode marker = contextData.getMarker();
    CoreExpression expectedType = contextData.getExpectedType();
    ConcreteFactory factory = ext.factory.withData(marker);
    List<CoreBinding> vars = typechecker.getFreeBindingsList();
    if (!contextData.getArguments().isEmpty() && !contextData.getArguments().get(0).isExplicit()) {
      ConcreteExpression arg = contextData.getArguments().get(0).getExpression();
      if (arg instanceof ConcreteNumberExpression) {
        BigInteger index = ((ConcreteNumberExpression) arg).getNumber();
        if (index.compareTo(BigInteger.ONE) < 0) {
          typechecker.getErrorReporter().report(new TypecheckingError("The index should be positive", arg));
          return null;
        }
        if (index.compareTo(BigInteger.valueOf(vars.size())) > 0) {
          typechecker.getErrorReporter().report(new TypecheckingError("The index should be <= " + vars.size(), arg));
          return null;
        }
        return typechecker.typecheck(factory.app(factory.ref(vars.get(vars.size() - index.intValue())), contextData.getArguments().subList(1, contextData.getArguments().size())), expectedType);
      } else {
        typechecker.getErrorReporter().report(new TypecheckingError("Expected a number", arg));
        return null;
      }
    }

    for (ConcreteArgument argument : contextData.getArguments()) {
      typechecker.getErrorReporter().report(new IgnoredArgumentError(argument.getExpression()));
    }

    if (expectedType == null) {
      typechecker.getErrorReporter().report(new TypecheckingError("Cannot infer the expected type", marker));
      return null;
    }

    CoreBinding binding = typechecker.withCurrentState(tc -> {
      for (int i = vars.size() - 1; i >= 0; i--) {
        CoreBinding var = vars.get(i);
        CoreBinding result = Utils.tryWithSavedState(tc, tc2 -> tc2.compare(var.getTypeExpr(), expectedType, CMP.LE, marker, false, true, false) ? var : null);
        if (result != null) return result;
      }
      return null;
    });

    if (binding == null) {
      typechecker.getErrorReporter().report(new TypecheckingError("Cannot find a proof in the context", marker));
      return null;
    }

    return typechecker.typecheck(factory.ref(binding), expectedType);
  }
}
