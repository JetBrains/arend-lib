package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;
import org.arend.lib.meta.equation.datafactory.GroupDataFactory;
import org.arend.lib.util.Values;

public abstract class GroupRuleBase implements SimplificationRule {
  protected final Values<CoreExpression> values;
  protected final ConcreteFactory factory;
  protected final StdExtension ext;
  protected final FunctionMatcher mulMatcher;
  protected final FunctionMatcher ideMatcher;
  protected final FunctionMatcher invMatcher;
  protected final boolean isAdditive;
  protected final boolean isCommutative;
  protected final TypedExpression instance;
  protected final ArendRef dataRef;

  public GroupRuleBase(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ConcreteReferenceExpression refExpr, ExpressionTypechecker typechecker, boolean isAdditive, boolean isCommutative) {
    this.values = new Values<>(typechecker, refExpr);
    this.factory = ext.factory;
    this.ext = ext;
    if (isAdditive) {
      var convertedInst = typechecker.typecheck(factory.appBuilder(factory.ref(isCommutative ? ext.equationMeta.fromAbGroupToCGroup.getRef() : ext.equationMeta.fromAddGroupToGroup.getRef())).app(factory.core(instance)).build(), null);
      this.instance = convertedInst != null ? convertedInst : instance;
    } else {
      this.instance = instance;
    }
    this.isAdditive = isAdditive;
    this.isCommutative = isCommutative;
    this.dataRef = factory.local("d");
    if (isAdditive) {
      this.mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.plus, typechecker, factory, refExpr, ext, 2);
      this.invMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.negative, typechecker, factory, refExpr, ext, 1);
      this.ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.zro, typechecker, factory, refExpr, ext, 0);
    } else {
      this.mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.mul, typechecker, factory, refExpr, ext, 2);
      this.invMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.inverse, typechecker, factory, refExpr, ext, 1);
      this.ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.ide, typechecker, factory, refExpr, ext, 0);
    }
  }

  @Override
  public ConcreteExpression finalizeEqProof(ConcreteExpression proof) {
    var dataFactory = new GroupDataFactory(ext.equationMeta, dataRef, values, factory, instance, isCommutative, !isAdditive);
    return dataFactory.wrapWithData(proof);
  }
}
