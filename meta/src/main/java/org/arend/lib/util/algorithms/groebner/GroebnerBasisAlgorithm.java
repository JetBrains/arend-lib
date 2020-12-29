package org.arend.lib.util.algorithms.groebner;

import org.arend.lib.util.algorithms.polynomials.Poly;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

public interface GroebnerBasisAlgorithm {
  Map<Poly<BigInteger>, List<Poly<BigInteger>>> computeGBwCoefficients(List<Poly<BigInteger>> generators);
}
