package org.arend.lib.util.algorithms.polynomials;

import java.math.BigInteger;

public interface Ring<E> {
    E add(E a, E b);
    E subtr(E a, E b);
    E mul(E a, E b);
    E unit();
    E zero();

    static <E> E negUnit(Ring<E> ring) { return ring.subtr(ring.zero(), ring.unit()); }

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
    };
}
