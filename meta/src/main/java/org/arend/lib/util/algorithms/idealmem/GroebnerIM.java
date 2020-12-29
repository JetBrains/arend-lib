package org.arend.lib.util.algorithms.idealmem;

import org.arend.lib.util.algorithms.groebner.GroebnerBasisAlgorithm;
import org.arend.lib.util.algorithms.polynomials.Poly;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

public class GroebnerIM implements IdealMembership {
  private final GroebnerBasisAlgorithm gbAlg;

  public GroebnerIM(GroebnerBasisAlgorithm gbAlg) {
    this.gbAlg = gbAlg;
  }

  @Override
  public List<Poly<BigInteger>> computeGenDecomposition(Poly<BigInteger> poly, List<Poly<BigInteger>> generators) {
    var groebnerBasisCoeffs = gbAlg.computeGBwCoefficients(generators);
    var groebnerBasis = new ArrayList<>(groebnerBasisCoeffs.keySet());
    var divResult = poly.divideWRemainder(groebnerBasis);
    if (!divResult.get(divResult.size() - 1).isZero()) {
      return null;
    }
    var decompositionCoeffs = new ArrayList<Poly<BigInteger>>();
    for (int i = 0; i < generators.size(); ++i) {
      var coeff = Poly.constant(poly.ring().zero(), poly.numVars(), poly.ring());
      for (int j = 0; j < divResult.size() - 1; ++j) {
        coeff = coeff.add(groebnerBasisCoeffs.get(groebnerBasis.get(j)).get(i).mul((Poly<BigInteger>) divResult.get(j)));
      }
      decompositionCoeffs.add(coeff);
    }
    return decompositionCoeffs;
  }
}
