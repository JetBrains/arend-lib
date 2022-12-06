package org.arend.lib.meta.equation.datafactory;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.meta.equation.EquationMeta;
import org.arend.lib.util.Values;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static java.util.Collections.singletonList;

public abstract class DataFactoryBase implements DataFactory {
  protected final EquationMeta meta;
  protected final ConcreteFactory factory;
  protected CoreFunCallExpression equality;
  protected final TypedExpression instance;
  protected final Values<CoreExpression> values;
  protected final ArendRef dataRef;
  protected final List<ConcreteLetClause> letClauses;

  public DataFactoryBase(EquationMeta meta, ArendRef dataRef, Values<CoreExpression> values, ConcreteFactory factory, TypedExpression instance) {
    this.meta = meta;
    this.factory = factory;
    this.instance = instance;
    //dataRef = factory.local("d");
    this.dataRef = dataRef;
    letClauses = new ArrayList<>();
    letClauses.add(null);
    this.values = values;
  }
  protected abstract ConcreteExpression getDefaultValue();
  protected abstract ConcreteExpression getDataClass(ConcreteExpression instanceArg, ConcreteExpression dataArg);

  public static ConcreteExpression makeFin(int n, ConcreteFactory factory, ArendRef fin) {
    return factory.app(factory.ref(fin), true, factory.number(n));
  }
  public static ConcreteExpression makeLambda(Values<CoreExpression> values, ConcreteFactory factory, EquationMeta meta) {
    ArendRef lamParam = factory.local("j");
    List<CoreExpression> valueList = values.getValues();
    ConcreteClause[] caseClauses = new ConcreteClause[valueList.size()];
    for (int i = 0; i < valueList.size(); i++) {
      caseClauses[i] = factory.clause(singletonList(factory.numberPattern(i)), factory.core(valueList.get(i).computeTyped()));
    }
    return factory.lam(singletonList(factory.param(singletonList(lamParam), makeFin(valueList.size(), factory, meta.ext.prelude.getFin().getRef()))),
            factory.caseExpr(false, singletonList(factory.caseArg(factory.ref(lamParam), null, null)), null, null, caseClauses));
  }

  @Override
  public ConcreteExpression wrapWithData(ConcreteExpression expression) {
    /*
    ArendRef lamParam = factory.local("n");
    List<CoreExpression> valueList = values.getValues();
    ConcreteClause[] caseClauses = new ConcreteClause[valueList.size() + 1];
    for (int i = 0; i < valueList.size(); i++) {
      caseClauses[i] = factory.clause(singletonList(factory.numberPattern(i)), factory.core(null, valueList.get(i).computeTyped()));
    }
    caseClauses[valueList.size()] = factory.clause(singletonList(factory.refPattern(null, null)), getDefaultValue());

    ConcreteExpression instanceArg = factory.core(instance);
    ConcreteExpression dataArg = factory.lam(singletonList(factory.param(singletonList(lamParam), factory.ref(meta.ext.prelude.getNat().getRef()))),
            factory.caseExpr(false, singletonList(factory.caseArg(factory.ref(lamParam), null, null)), null, null, caseClauses));

    letClauses.set(0, factory.letClause(dataRef, Collections.emptyList(), null, factory.newExpr(getDataClass(instanceArg, dataArg))));
    //return typechecker.typecheck(meta.ext.factory.letExpr(false, false, letClauses, expression), null);
    return meta.ext.factory.letExpr(false, false, letClauses, expression); */
    List<CoreExpression> valueList = values.getValues();

    ConcreteExpression instanceArg = factory.core(instance);
    ConcreteExpression dataArg = factory.ref(meta.ext.prelude.getEmptyArray().getRef());
    for (int i = valueList.size() - 1; i >= 0; i--) {
      dataArg = factory.app(factory.ref(meta.ext.prelude.getArrayCons().getRef()), true, factory.core(null, valueList.get(i).computeTyped()), dataArg);
    }

    letClauses.set(0, factory.letClause(dataRef, Collections.emptyList(), null, factory.newExpr(getDataClass(instanceArg, dataArg))));
    return meta.ext.factory.letExpr(false, false, letClauses, expression);
  }
}
