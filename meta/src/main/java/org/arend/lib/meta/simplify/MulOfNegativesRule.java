package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;

import java.util.List;

public class MulOfNegativesRule extends LocalSimplificationRuleBase {
  private final FunctionMatcher mulMatcher;
  private final FunctionMatcher negativeMatcher;

  public MulOfNegativesRule(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ConcreteReferenceExpression refExpr, ExpressionTypechecker typechecker) {
    super(instance, classCall, ext, refExpr, typechecker);
    this.mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.mul, typechecker, factory, refExpr, ext, 2);
    this.negativeMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.negative, typechecker, factory, refExpr, ext, 1);
  }

  @Override
  protected Pair<CoreExpression, ConcreteExpression> simplifySubexpression(CoreExpression subexpr) {
    List<CoreExpression> args = mulMatcher.match(subexpr);
    if (args != null) {
      var left = args.get(args.size() - 2);
      var right = args.get(args.size() - 1);
      args = negativeMatcher.match(left);
      boolean isNegOnTheLeft = args != null;
      if (args == null) {
        args = negativeMatcher.match(right);
        if (args == null) {
          return null;
        }
      }
      var firstValue = isNegOnTheLeft ? args.get(0) : left;
      var secondValue = isNegOnTheLeft ? right : args.get(0);
      ConcreteExpression negPath = isNegOnTheLeft ? factory.ref(ext.equationMeta.negMulLeft.getRef()) : factory.ref(ext.equationMeta.negMulRight.getRef());

      if (firstValue != null) {
        var subexprPath = factory.appBuilder(negPath)
                .app(factory.hole(), false)
                .app(factory.core(firstValue.computeTyped()), false)
                .app(factory.core(secondValue.computeTyped()), false).build();
        var newExpr = factory.appBuilder(factory.ref(ext.equationMeta.negative.getRef())).
                app(factory.appBuilder(factory.ref(ext.equationMeta.mul.getRef())).app(factory.core(firstValue.computeTyped())).app(factory.core(secondValue.computeTyped())).build()).build();
        var checkedNewExpr = typechecker.typecheck(newExpr, subexpr.computeType());
        if (checkedNewExpr == null) return null;
        return new Pair<>(checkedNewExpr.getExpression(), subexprPath);
      }
    }
    return null;
  }
}
