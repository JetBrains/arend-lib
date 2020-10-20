package org.arend.lib.util.algorithms.idealmem;

import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.multivar.MultivariatePolynomial;

import java.util.List;

public interface IdealMembership {
    List<MultivariatePolynomial<BigInteger>> computeGenDecomposition(MultivariatePolynomial<BigInteger> poly, List<MultivariatePolynomial<BigInteger>> generators);
}
