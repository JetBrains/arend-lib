package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
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

import java.util.ArrayList;
import java.util.List;

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
    List<? extends ConcreteArgument> oldArgs = contextData.getArguments();
    if (!checkArguments(oldArgs, resolver.getErrorReporter(), contextData.getMarker(), argumentExplicitness())) {
      return null;
    }

    ConcreteCoclauses coclauses = contextData.getCoclauses();
    if (coclauses != null && oldArgs.isEmpty()) {
      resolver.getErrorReporter().report(new NameResolverError("Expected a class name", coclauses));
      return null;
    }

    if (oldArgs.isEmpty()) {
      return contextData.getReferenceExpression();
    }

    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());
    List<ConcreteArgument> args = new ArrayList<>();
    for (int i = 0; i < oldArgs.size() - 1; i++) {
      ConcreteArgument oldArg = oldArgs.get(i);
      args.add(factory.arg(resolver.resolve(oldArg.getExpression()), oldArg.isExplicit()));
    }
    ConcreteArgument arg = oldArgs.get(oldArgs.size() - 1);
    args.add(factory.arg(resolver.resolve(coclauses == null ? arg.getExpression() : factory.classExt(arg.getExpression(), coclauses.getCoclauseList())), arg.isExplicit()));
    return factory.app(contextData.getReferenceExpression(), args);
  }
}
