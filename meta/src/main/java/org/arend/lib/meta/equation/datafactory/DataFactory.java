package org.arend.lib.meta.equation.datafactory;

import org.arend.ext.concrete.expr.ConcreteExpression;

public interface DataFactory {
  ConcreteExpression wrapWithData(ConcreteExpression expression);
}
