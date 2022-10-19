package org.arend.lib.meta.linear;

import org.arend.ext.core.expr.CoreExpression;

import java.math.BigInteger;

public class Equation<E> {
  public final CoreExpression instance;
  public final Operation operation;
  public final E lhsTerm;
  public final E rhsTerm;

  public enum Operation { LESS, LESS_OR_EQUALS, EQUALS }

  public Equation(CoreExpression instance, Operation operation, E lhsTerm, E rhsTerm) {
    this.instance = instance;
    this.operation = operation;
    this.lhsTerm = lhsTerm;
    this.rhsTerm = rhsTerm;
  }

  public BigInteger getLCM() {
    return BigInteger.ONE;
  }
}
