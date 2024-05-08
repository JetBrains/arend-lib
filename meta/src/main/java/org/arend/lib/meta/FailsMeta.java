package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreInferenceReferenceExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.error.MetaDidNotFailError;
import org.arend.lib.meta.util.MetaInvocationMeta;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;
import java.util.Objects;

public class FailsMeta extends MetaInvocationMeta {
  private final StdExtension ext;

  public FailsMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { false, true };
  }

  private ConcreteExpression makeResult(Object data) {
    return ext.factory.withData(data).tuple();
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return makeResult(null);
  }

  @Override
  public TypedExpression invokeMeta(MetaDefinition meta, List<ConcreteExpression> implicitArgs, ExpressionTypechecker typechecker, ContextData contextData) {
    if (!implicitArgs.isEmpty()) {
      TypedExpression type = typechecker.typecheck(implicitArgs.get(0), null);
      if (type == null) {
        return null;
      }
      contextData.setExpectedType(type.getExpression());
    }

    ErrorReporter errorReporter = typechecker.getErrorReporter();
    boolean[] hasErrors = new boolean[] { false };
    TypedExpression result = typechecker.withErrorReporter(error -> hasErrors[0] = true, tc -> meta.checkAndInvokeMeta(tc, contextData));

    if (result == null || hasErrors[0]) {
      return typechecker.typecheck(makeResult(contextData.getReferenceExpression().getData()), null);
    }

    // If the meta is deferred, it won't fail immediately.
    // To fix this, we defer ourselves and check if there were any errors later.
    if (result.getExpression() instanceof CoreInferenceReferenceExpression) {
      return typechecker.defer(new MetaDefinition() {
        @Override
        public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          if (!hasErrors[0]) {
            errorReporter.report(new MetaDidNotFailError(typechecker.getExpressionPrettifier(), result.getExpression(), contextData.getReferenceExpression()));
          }
          return typechecker.typecheck(makeResult(contextData.getReferenceExpression().getData()), null);
        }
      }, contextData, Objects.requireNonNull(typechecker.typecheck(ext.factory.sigma(), null)).getExpression(), true);
    }

    errorReporter.report(new MetaDidNotFailError(typechecker.getExpressionPrettifier(), result.getExpression(), contextData.getReferenceExpression()));
    return null;
  }
}
