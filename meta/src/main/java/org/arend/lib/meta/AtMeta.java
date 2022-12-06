package org.arend.lib.meta;

import org.arend.ext.FreeBindingsModifier;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

public class AtMeta extends BaseMetaDefinition implements MetaResolver {
  private final StdExtension ext;

  public AtMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean[] argumentExplicitness() {
    return new boolean[] { true, true, true };
  }

  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    return Utils.resolvePrefixAsInfix(this, resolver, contextData, ext.factory);
  }

  @Override
  public @Nullable ConcreteExpression resolveInfix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData, @Nullable ConcreteExpression leftArg, @Nullable ConcreteExpression rightArg) {
    if (leftArg == null || rightArg == null || !contextData.getArguments().isEmpty()) return Utils.normalResolve(resolver, contextData, leftArg, rightArg, ext.factory);

    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    ConcreteExpression cReplacement = resolver.resolve(rightArg);
    for (ConcreteExpression function : Utils.getArgumentList(resolver.resolve(leftArg))) {
      cReplacement = factory.app(function, true, cReplacement);
    }

    return factory.app(contextData.getReferenceExpression(), true, cReplacement, rightArg);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    CoreBinding binding = args.get(1).getExpression() instanceof ConcreteReferenceExpression ? typechecker.getFreeBinding(((ConcreteReferenceExpression) args.get(1).getExpression()).getReferent()) : null;
    if (binding == null) {
      typechecker.getErrorReporter().report(new TypecheckingError("Expected a local variable", args.get(1).getExpression()));
      return null;
    }

    TypedExpression replacement = typechecker.typecheck(args.get(0).getExpression(), null);
    if (replacement == null) {
      return null;
    }

    return typechecker.withFreeBindings(new FreeBindingsModifier().replace(binding, replacement.makeEvaluatingBinding(binding.getName())), tc -> tc.typecheck(args.get(2).getExpression(), contextData.getExpectedType()));
  }
}
