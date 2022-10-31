package org.arend.lib.ring;

import java.math.BigInteger;

public class IntRing implements Ring {
  public final BigInteger number;

  public final static IntRing ZERO = new IntRing(BigInteger.ZERO);
  public final static IntRing ONE = new IntRing(BigInteger.ONE);

  public IntRing(BigInteger number) {
    this.number = number;
  }

  @Override
  public IntRing add(Ring x) {
    return new IntRing(number.add(((IntRing) x).number));
  }

  @Override
  public IntRing multiply(Ring x) {
    return new IntRing(number.multiply(((IntRing) x).number));
  }

  @Override
  public IntRing negate() {
    return new IntRing(number.negate());
  }

  @Override
  public IntRing subtract(Ring x) {
    return new IntRing(number.subtract(((IntRing) x).number));
  }
}
