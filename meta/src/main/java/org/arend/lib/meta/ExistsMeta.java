package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.error.ArgumentExplicitnessError;
import org.arend.ext.error.NameResolverError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ExistsMeta implements MetaResolver, MetaDefinition {
  private final StdExtension ext;

  public ExistsMeta(StdExtension ext) {
    this.ext = ext;
  }

  private boolean getRef(ConcreteExpression expr, ExpressionResolver resolver, List<ArendRef> refs) {
    if (expr instanceof ConcreteReferenceExpression) {
      ArendRef ref = ((ConcreteReferenceExpression) expr).getReferent();
      if (resolver.isLongUnresolvedReference(ref)) {
        return false;
      }
      refs.add(ref);
      return true;
    }

    if (expr instanceof ConcreteHoleExpression) {
      refs.add(null);
      return true;
    }

    return false;
  }

  private List<ArendRef> getRefs(ConcreteExpression expr, ExpressionResolver resolver) {
    List<ArendRef> result = new ArrayList<>();
    for (ConcreteArgument argument : expr.getArgumentsSequence()) {
      if (!argument.isExplicit() || !getRef(argument.getExpression(), resolver, result)) {
        resolver.getErrorReporter().report(new NameResolverError("Cannot parse references", expr));
        return null;
      }
    }
    return result;

  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    if (!new ContextDataChecker().checkContextData(contextData, resolver.getErrorReporter())) {
      return null;
    }
    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());

    List<? extends ConcreteArgument> arguments = contextData.getArguments();
    if (arguments.isEmpty()) {
      return factory.sigma();
    }

    if (arguments.size() == 1) {
      if (!arguments.get(0).isExplicit()) {
        resolver.getErrorReporter().report(new ArgumentExplicitnessError(true, arguments.get(0).getExpression()));
        return null;
      }
      return factory.app(contextData.getReferenceExpression(), true, Collections.singletonList(resolver.resolve(arguments.get(0).getExpression())));
    }

    List<ConcreteParameter> parameters = new ArrayList<>();
    for (ConcreteArgument argument : arguments) {
      if (argument.isExplicit()) {
        if (argument.getExpression() instanceof ConcreteTypedExpression) {
          ConcreteTypedExpression typedExpr = (ConcreteTypedExpression) argument.getExpression();
          List<ArendRef> refs = getRefs(typedExpr.getExpression(), resolver);
          if (refs == null) {
            return null;
          }
          parameters.add(factory.param(refs, typedExpr.getType()));
        } else {
          parameters.add(factory.param(Collections.emptyList(), argument.getExpression()));
        }
      } else {
        List<ArendRef> refs = getRefs(argument.getExpression(), resolver);
        if (refs == null) {
          return null;
        }
        parameters.add(factory.param(refs, factory.hole()));
      }
    }
    return resolver.resolve(factory.app(contextData.getReferenceExpression(), true, Collections.singletonList(resolver.resolve(factory.sigma(parameters)))));
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());
    return typechecker.typecheck(factory.app(factory.ref(ext.TruncP.getRef()), contextData.getArguments()), contextData.getExpectedType());
  }
}
