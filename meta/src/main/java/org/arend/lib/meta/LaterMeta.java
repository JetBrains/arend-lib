package org.arend.lib.meta;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.*;
import org.arend.lib.meta.util.MetaInvocationMeta;

import java.util.List;

public class LaterMeta extends MetaInvocationMeta {
  @Override
  public boolean requireExpectedType() {
    return true;
  }

  @Override
  public TypedExpression invokeMeta(MetaDefinition meta, List<ConcreteExpression> implicitArgs, ExpressionTypechecker typechecker, ContextData contextData) {
    return typechecker.defer(meta, contextData, contextData.getExpectedType(), false);
  }
}
