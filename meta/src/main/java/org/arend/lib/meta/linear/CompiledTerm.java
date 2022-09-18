package org.arend.lib.meta.linear;

import org.arend.ext.concrete.expr.ConcreteExpression;

import java.math.BigInteger;
import java.util.List;

public class CompiledTerm {
  public final ConcreteExpression concrete;
  public final List<BigInteger> coefficients;
  public final BigInteger freeCoef;

  public CompiledTerm(ConcreteExpression concrete, List<BigInteger> coefficients, BigInteger freeCoef) {
    this.concrete = concrete;
    this.coefficients = coefficients;
    this.freeCoef = freeCoef;
  }
}
