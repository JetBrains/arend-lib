package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteCoclauses;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.error.NameResolverError;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ContextDataChecker;
import org.arend.ext.typechecking.MetaResolver;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;

public class ClassExtResolver extends ContextDataChecker implements MetaResolver {
  private final StdExtension ext;

  public ClassExtResolver(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    if (!checkArguments(contextData.getArguments(), resolver.getErrorReporter(), contextData.getMarker(), argumentExplicitness())) {
      return null;
    }

    ConcreteCoclauses coclauses = contextData.getCoclauses();
    if (coclauses != null && contextData.getArguments().isEmpty()) {
      resolver.getErrorReporter().report(new NameResolverError("Expected a class name", coclauses));
      return null;
    }

    if (contextData.getArguments().isEmpty()) {
      return contextData.getReferenceExpression();
    }

    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());
    ConcreteExpression arg = contextData.getArguments().get(0).getExpression();
    return factory.app(contextData.getReferenceExpression(), true, Collections.singletonList(resolver.resolve(coclauses == null ? arg : factory.classExt(arg, coclauses.getCoclauseList()))));
  }
}
