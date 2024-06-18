package org.arend.lib.meta.linear;

import org.arend.ext.concrete.expr.ConcreteExpression;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;

public record CompiledTerm(ConcreteExpression concrete, List<BigInteger> coefficients, Set<Integer> vars) {
  public BigInteger getCoef(int i) {
    return i < coefficients.size() ? coefficients.get(i) : BigInteger.ZERO;
  }
}
