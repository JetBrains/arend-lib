package org.arend.lib.meta.linear;

import org.arend.ext.concrete.expr.ConcreteExpression;

import java.math.BigInteger;
import java.util.List;

public class CompiledTerm {
  public final ConcreteExpression concrete;
  public final List<BigInteger> coefficients;

  public CompiledTerm(ConcreteExpression concrete, List<BigInteger> coefficients) {
    this.concrete = concrete;
    this.coefficients = coefficients;
  }

  public BigInteger getCoef(int i) {
    return i < coefficients.size() ? coefficients.get(i) : BigInteger.ZERO;
  }
}
