package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.meta.RewriteMeta;

public interface SimplificationRule {
  /**
   * @return Pair (simplifiedExpr, p : simplifiedExpr = expression). Null if expression cannot be simplified.
   */
  RewriteMeta.EqProofConcrete apply(TypedExpression expression);

  ConcreteExpression finalizeEqProof(ConcreteExpression proof);
}
