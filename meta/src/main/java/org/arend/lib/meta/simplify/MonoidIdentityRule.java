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

public class MonoidIdentityRule extends LocalSimplificationRuleBase {
  private final FunctionMatcher mulMatcher;
  private final FunctionMatcher ideMatcher;
  private final CoreClassField ideLeft;
  private final CoreClassField ideRight;

  private final boolean isAdditive;

  public MonoidIdentityRule(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ConcreteReferenceExpression refExpr, ExpressionTypechecker typechecker, boolean isAdditive) {
    super(instance, classCall, ext, refExpr, typechecker);
    this.isAdditive = isAdditive;
    if (isAdditive) {
      this.mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.plus, typechecker, factory, refExpr, ext, 2);
      this.ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.zro, typechecker, factory, refExpr, ext, 0);
      this.ideLeft = ext.equationMeta.addMonZroLeft;
      this.ideRight = ext.equationMeta.addMonZroRight;
    } else {
      this.mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.mul, typechecker, factory, refExpr, ext, 2);
      this.ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.ide, typechecker, factory, refExpr, ext, 0);
      this.ideLeft = ext.equationMeta.ideLeft;
      this.ideRight = ext.equationMeta.ideRight;
    }
  }

  @Override
  protected Pair<CoreExpression, ConcreteExpression> simplifySubexpression(CoreExpression subexpr) {
    List<CoreExpression> args = mulMatcher.match(subexpr);
    if (args != null) {
      var left = args.get(args.size() - 2);
      var right = args.get(args.size() - 1);
      boolean isIdeOnTheLeft = ideMatcher.match(left) != null;
      var ide = isIdeOnTheLeft ? left : ideMatcher.match(right) != null ? right : null;
      var value = ide == left ? right : left;
      ConcreteExpression idePath = isIdeOnTheLeft ? factory.ref(ideLeft.getRef()) : factory.ref(ideRight.getRef());

      if (ide != null) {
        var subexprPath = factory.appBuilder(idePath).app(factory.hole(), false).app(factory.core(value.computeTyped()), false).build();
        return new Pair<>(value, subexprPath);
      }
    }
    return null;
  }

  @Override
  public boolean equals(Object obj) {
    if (obj instanceof MonoidIdentityRule rule) {
      return isAdditive == rule.isAdditive;
    }
    return false;
  }
}
