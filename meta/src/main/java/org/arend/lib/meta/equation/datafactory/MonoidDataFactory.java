package org.arend.lib.meta.equation.datafactory;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.meta.equation.EquationMeta;
import org.arend.lib.util.Values;

import java.util.Arrays;
import java.util.List;

public class MonoidDataFactory extends DataFactoryBase {
  private final boolean isSemilattice;
  private final boolean isCommutative;
  private final CoreClassField ide;

  public MonoidDataFactory(EquationMeta meta, ArendRef dataRef, Values<CoreExpression> values, List<ConcreteLetClause> letClauses, ConcreteFactory factory, TypedExpression instance, boolean isSemilattice, boolean isCommutative, boolean isMultiplicative) {
    super(meta, dataRef, values, factory, instance);
    this.letClauses.addAll(letClauses);
    this.isSemilattice = isSemilattice;
    this.isCommutative = isCommutative;
    ide = isSemilattice ? meta.top : isMultiplicative ? meta.ide : meta.zro;
  }
  @Override
  protected ConcreteExpression getDataClass(ConcreteExpression instanceArg, ConcreteExpression dataArg) {
    ConcreteExpression data = factory.ref((isSemilattice ? meta.LData : isCommutative ? meta.CData : meta.Data).getRef());
    return isSemilattice
            ? factory.classExt(data, Arrays.asList(factory.implementation(meta.SemilatticeDataCarrier.getRef(), instanceArg), factory.implementation(meta.DataFunction.getRef(), dataArg)))
            : factory.app(data, Arrays.asList(factory.arg(instanceArg, false), factory.arg(dataArg, true)));
  }

  @Override
  protected ConcreteExpression getDefaultValue() {
    return factory.ref(ide.getRef());
  }
}
