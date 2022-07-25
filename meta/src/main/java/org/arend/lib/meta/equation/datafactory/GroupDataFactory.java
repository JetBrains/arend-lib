package org.arend.lib.meta.equation.datafactory;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.meta.equation.EquationMeta;
import org.arend.lib.util.Values;

import java.util.Arrays;

public class GroupDataFactory extends DataFactoryBase {
  private final boolean isCommutative;
  private final CoreClassField ide;

  public GroupDataFactory(EquationMeta meta, ArendRef dataRef, Values<CoreExpression> values, ConcreteFactory factory, TypedExpression instance, boolean isCommutative, boolean isMultiplicative) {
    super(meta, dataRef, values, factory, instance);
    this.isCommutative = isCommutative;
    ide = isMultiplicative ? meta.ide : meta.zro;
  }

  @Override
  protected ConcreteExpression getDefaultValue() {
    return factory.ref(ide.getRef());
  }

  @Override
  protected ConcreteExpression getDataClass(ConcreteExpression instanceArg, ConcreteExpression dataArg) {
    ConcreteExpression data = factory.ref((isCommutative ? meta.CGroupData : meta.GroupData).getRef());
    return factory.app(data, Arrays.asList(factory.arg(instanceArg, false), factory.arg(dataArg, true)));
  }
}
