package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.error.NameResolverError;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;
import java.util.List;

public class RunMeta extends BaseMetaDefinition implements MetaResolver {
  private final StdExtension ext;

  public RunMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { false };
  }

  @Override
  public boolean allowEmptyCoclauses() {
    return true;
  }

  private ConcreteExpression getConcreteRepresentation(List<? extends ConcreteArgument> arguments, ConcreteSourceNode marker) {
    List<? extends ConcreteExpression> args = Utils.getArgumentList(arguments.get(0).getExpression());
    ConcreteFactory factory = ext.factory.withData(marker);
    ConcreteExpression result = args.get(args.size() - 1);
    for (int i = args.size() - 2; i >= 0; i--) {
      ConcreteExpression arg = args.get(i);
      if (arg instanceof ConcreteLetExpression && ((ConcreteLetExpression) arg).getExpression() instanceof ConcreteIncompleteExpression) {
        ConcreteLetExpression let = (ConcreteLetExpression) arg;
        result = factory.letExpr(let.isHave(), let.isStrict(), let.getClauses(), result);
      } else if (arg instanceof ConcreteLamExpression && ((ConcreteLamExpression) arg).getBody() instanceof ConcreteIncompleteExpression) {
        result = factory.lam(((ConcreteLamExpression) arg).getParameters(), result);
      } else {
        result = factory.app(arg, true, Collections.singletonList(result));
      }
    }
    return result;
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return getConcreteRepresentation(arguments, null);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    if (contextData.getExpectedType() != null) {
      return typechecker.defer(new MetaDefinition() {
        @Override
        public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          return typechecker.typecheck(RunMeta.this.getConcreteRepresentation(contextData.getArguments(), contextData.getMarker()), contextData.getExpectedType());
        }
      }, contextData, contextData.getExpectedType(), false);
    } else {
      return typechecker.typecheck(getConcreteRepresentation(contextData.getArguments(), contextData.getMarker()), contextData.getExpectedType());
    }
  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    if (!checkContextData(contextData, resolver.getErrorReporter())) {
      return null;
    }
    if (contextData.getArguments().isEmpty() == (contextData.getCoclauses() == null)) {
      resolver.getErrorReporter().report(new NameResolverError("Expected 1 implicit argument", contextData.getMarker()));
      return null;
    }
    if (contextData.getCoclauses() != null) {
      return ext.factory.withData(contextData.getCoclauses().getData()).goal();
    }

    return resolver.resolve(getConcreteRepresentation(contextData.getArguments(), contextData.getReferenceExpression()));
  }
}
