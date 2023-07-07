package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;

import java.util.List;

public class IdentityInverseRule extends LocalSimplificationRuleBase {
  private final FunctionMatcher invMatcher;
  private final FunctionMatcher ideMatcher;
  private final CoreFunctionDefinition invIde;

  public IdentityInverseRule(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ConcreteReferenceExpression refExpr, ExpressionTypechecker typechecker, boolean isAdditive) {
    super(instance, classCall, ext, refExpr, typechecker);
    if (isAdditive) {
      this.invMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.negative, typechecker, factory, refExpr, ext, 1);
      this.ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.zro, typechecker, factory, refExpr, ext, 0);
      this.invIde = ext.equationMeta.negativeZro;
    } else {
      this.invMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.inverse, typechecker, factory, refExpr, ext, 1);
      this.ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.ide, typechecker, factory, refExpr, ext, 0);
      this.invIde = ext.equationMeta.invIde;
    }
  }

  @Override
  protected Pair<CoreExpression, ConcreteExpression> simplifySubexpression(CoreExpression subexpr) {
    List<CoreExpression> args = invMatcher.match(subexpr);
    if (args != null) {
      var arg = args.get(0);
      if (ideMatcher.match(arg) != null) {
        return new Pair<>(arg, factory.ref(invIde.getRef()));
      }
    }
    return null;
  }
}
