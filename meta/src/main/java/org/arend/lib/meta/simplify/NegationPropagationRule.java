package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;

import java.util.List;

public class NegationPropagationRule extends LocalSimplificationRuleBase {
  private final FunctionMatcher mulMatcher;
  private final FunctionMatcher invMatcher;
  private final boolean isAdditive;

  public NegationPropagationRule(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ConcreteReferenceExpression refExpr, ExpressionTypechecker typechecker, boolean isAdditive) {
    super(instance, classCall, ext, refExpr, typechecker);
    this.isAdditive = isAdditive;
    if (isAdditive) {
      this.mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.plus, typechecker, factory, refExpr, ext, 2);
      this.invMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.negative, typechecker, factory, refExpr, ext, 1);
    } else {
      this.mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.mul, typechecker, factory, refExpr, ext, 2);
      this.invMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.inverse, typechecker, factory, refExpr, ext, 1);
    }
  }

  @Override
  protected Pair<CoreExpression, ConcreteExpression> simplifySubexpression(CoreExpression subexpr) {
    List<CoreExpression> args = invMatcher.match(subexpr);
    if (args != null) {
      args = mulMatcher.match(args.get(0));
      if (args != null) {
        var left = args.get(args.size() - 2);
        var right = args.get(args.size() - 1);
        var newLeft = factory.appBuilder(factory.ref(isAdditive ? ext.equationMeta.negative.getRef() : ext.equationMeta.inverse.getRef()))
          .app(factory.core(left.computeTyped())).build();
        var newRight = factory.appBuilder(factory.ref(isAdditive ? ext.equationMeta.negative.getRef() : ext.equationMeta.inverse.getRef()))
          .app(factory.core(right.computeTyped())).build();
        var newExpr = factory.appBuilder(factory.ref(isAdditive ? ext.equationMeta.plus.getRef() : ext.equationMeta.mul.getRef()))
          .app(newRight).app(newLeft).build();
        var checkedNewExpr = typechecker.typecheck(newExpr, subexpr.computeType());
        if (checkedNewExpr == null) return null;
        var negPropagationLemma = factory.ref(isAdditive ? ext.equationMeta.negativePlus.getRef() : ext.equationMeta.inverseMul.getRef());
        return new Pair<>(checkedNewExpr.getExpression(), factory.appBuilder(negPropagationLemma).app(factory.hole(), false).app(factory.core(left.computeTyped()), false).app(factory.core(right.computeTyped()), false).build());
      }
    }
    return null;
  }
}
