package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteAppBuilder;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteCaseArgument;
import org.arend.ext.concrete.expr.ConcreteCaseExpression;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.CoreCaseExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.UncheckedExpression;
import org.arend.ext.error.NameResolverError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class MatchingCasesMeta extends BaseMetaDefinition implements MetaResolver {
  private final StdExtension ext;

  public MatchingCasesMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false, true, true };
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    if (args.size() > 2) {
      resolver.getErrorReporter().report(new NameResolverError("Expected at most 2 arguments", contextData.getMarker()));
      return null;
    }
    if (args.size() == 2 && !(!args.get(0).isExplicit() && args.get(1).isExplicit())) {
      resolver.getErrorReporter().report(new NameResolverError("Expected 1 implicit and 1 explicit argument", contextData.getMarker()));
      return null;
    }

    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    ConcreteAppBuilder builder = factory.appBuilder(contextData.getReferenceExpression());
    if (!args.isEmpty() && !args.get(0).isExplicit()) {
      builder.app(resolver.resolve(args.get(0).getExpression()), args.get(0).isExplicit());
    }
    builder.app(resolver.resolve(factory.caseExpr(false, Collections.emptyList(), null, null, contextData.getClauses() == null ? Collections.emptyList() : contextData.getClauses().getClauseList())));
    if (args.size() == 1 && args.get(0).isExplicit()) {
      builder.app(resolver.resolve(args.get(0).getExpression()));
    } else if (args.size() > 1) {
      builder.app(resolver.resolve(args.get(1).getExpression()));
    }
    return builder.build();
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    ConcreteExpression marker = contextData.getMarker();
    ConcreteFactory factory = ext.factory.withData(marker);
    List<ArendRef> caseRefs = new ArrayList<>();
    List<ConcreteCaseArgument> caseArgs = new ArrayList<>();
    Deque<CoreExpression> subexpressions = new ArrayDeque<>();
    CoreExpression expectedType = contextData.getExpectedType();
    boolean[] isSCase = new boolean[] { false };
    expectedType.findSubexpression(expr -> {
      if (expr instanceof CoreCaseExpression) {
        if (((CoreCaseExpression) expr).isSCase()) {
          isSCase[0] = true;
        }
        for (CoreExpression argument : ((CoreCaseExpression) expr).getArguments()) {
          if (!(argument instanceof CoreCaseExpression)) {
            subexpressions.add(argument);
            TypedExpression typed = argument.computeTyped();
            ArendRef ref = factory.local(ext.renamerFactory.getNameFromType(typed.getType(), null));
            caseRefs.add(ref);
            caseArgs.add(factory.caseArg(factory.core(typed), ref, null));
          }
        }
      }
      return false;
    });

    if (subexpressions.isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError("Cannot find matching subexpressions", contextData.getMarker()));
      return null;
    }

    return typechecker.typecheck(factory.caseExpr(isSCase[0], caseArgs, factory.meta("case_return", new MetaDefinition() {
      @Override
      public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        UncheckedExpression result = expectedType.replaceSubexpressions(expr -> {
          if (!subexpressions.isEmpty() && subexpressions.getFirst() == expr) {
            CoreBinding binding = typechecker.getFreeBinding(caseRefs.get(caseRefs.size() - subexpressions.size()));
            subexpressions.removeFirst();
            return binding == null ? null : binding.makeReference();
          }
          return null;
        });
        if (result == null) {
          typechecker.getErrorReporter().report(new TypecheckingError("Cannot substitute expressions", marker));
          return null;
        }
        return typechecker.check(result, marker);
      }
    }), null, ((ConcreteCaseExpression) args.get(args.get(0).isExplicit() ? 0 : 1).getExpression()).getClauses()), contextData.getExpectedType());
  }
}
