package org.arend.lib.util.algorithms.polynomials;

import java.math.BigInteger;

public interface Ring<E> {
  E add(E a, E b);

  E subtr(E a, E b);

  E mul(E a, E b);

  E unit();

  E zero();

  int cmp(E a, E b);

  E div(E a, E b);

  E lcm(E a, E b);

  static <E> E negUnit(Ring<E> ring) {
    return ring.subtr(ring.zero(), ring.unit());
  }

  Ring<BigInteger> Z = new Ring<>() {
    @Override
    public BigInteger add(BigInteger a, BigInteger b) {
      return a.add(b);
    }

    @Override
    public BigInteger subtr(BigInteger a, BigInteger b) {
      return a.subtract(b);
    }

    @Override
    public BigInteger mul(BigInteger a, BigInteger b) {
      return a.multiply(b);
    }

    @Override
    public BigInteger unit() {
      return BigInteger.ONE;
    }

    @Override
    public BigInteger zero() {
      return BigInteger.ZERO;
    }

    @Override
    public int cmp(BigInteger a, BigInteger b) {
      return a.compareTo(b);
    }

    @Override
    public BigInteger div(BigInteger a, BigInteger b) {
      if (!a.abs().mod(b.abs()).equals(BigInteger.ZERO)) return null;
      return a.divide(b);
    }

    @Override
    public BigInteger lcm(BigInteger a, BigInteger b) {
      return a.multiply(b).divide(a.gcd(b));
    }
  };
}
