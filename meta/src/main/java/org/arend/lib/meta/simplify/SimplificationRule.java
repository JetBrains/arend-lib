package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.meta.RewriteMeta;

public interface SimplificationRule {
  /*class MaybeTypedConcreteExpr {
    public ConcreteExpression expression;
    public TypedExpression typed;

    public MaybeTypedConcreteExpr(ConcreteExpression expression, TypedExpression typed) {
      this.expression = expression;
      this.typed = typed;
    }
  } */

  /**
   * @return Pair (simplifiedExpr, p : simplifiedExpr = expression). Null if expression cannot be simplified.
   */
  RewriteMeta.EqProofConcrete apply(TypedExpression expression);
}
