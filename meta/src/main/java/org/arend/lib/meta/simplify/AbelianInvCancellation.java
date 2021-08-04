package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.util.Pair;

public class AbelianInvCancellation implements SimplificationRule {
  @Override
  public Pair<ConcreteExpression, ConcreteExpression> apply(TypedExpression expression) {
    return null;
  }
}
