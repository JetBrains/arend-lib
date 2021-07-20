package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Pair;
import org.jetbrains.annotations.NotNull;

import java.util.List;

public class SimplifyMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public SimplifyMeta(StdExtension ext) {
    this.ext = ext;
  }

  private Pair<ConcreteExpression, ConcreteExpression> simplifyExpression(TypedExpression expression) {

  }

  @Override
  public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    List<? extends ConcreteArgument> args = contextData.getArguments();
  }
}
