package org.arend.lib.util.algorithms.groebner;

import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.multivar.MultivariatePolynomial;

import java.util.List;
import java.util.Map;

public interface GroebnerBasisAlgorithm {
    Map<MultivariatePolynomial<BigInteger>, List<MultivariatePolynomial<BigInteger>>> computeGBwCoefficients(List<MultivariatePolynomial<BigInteger>> generators);
}
