package org.arend.lib.util.algorithms.idealmem;

import org.arend.lib.util.algorithms.polynomials.Poly;

import java.math.BigInteger;
import java.util.List;

public interface IdealMembership {
  List<Poly<BigInteger>> computeGenDecomposition(Poly<BigInteger> poly, List<Poly<BigInteger>> generators);
}
