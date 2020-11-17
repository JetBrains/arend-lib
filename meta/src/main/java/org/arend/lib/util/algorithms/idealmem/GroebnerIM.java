package org.arend.lib.util.algorithms.idealmem;

import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.multivar.MultivariateDivision;
import cc.redberry.rings.poly.multivar.MultivariatePolynomial;
import org.arend.lib.util.algorithms.groebner.GroebnerBasisAlgorithm;

import java.util.ArrayList;
import java.util.List;

public class GroebnerIM implements IdealMembership {
    private final GroebnerBasisAlgorithm gbAlg;

    public GroebnerIM(GroebnerBasisAlgorithm gbAlg) {
        this.gbAlg = gbAlg;
    }

    @Override
    @SuppressWarnings("unchecked")
    public List<MultivariatePolynomial<BigInteger>> computeGenDecomposition(MultivariatePolynomial<BigInteger> poly, List<MultivariatePolynomial<BigInteger>> generators) {
        var groebnerBasisCoeffs = gbAlg.computeGBwCoefficients(generators);
        var groebnerBasis = new ArrayList<>(groebnerBasisCoeffs.keySet());
        var divResult = MultivariateDivision.divideAndRemainder(poly, groebnerBasis.toArray(new MultivariatePolynomial[0]));
        if (!divResult[divResult.length - 1].isZero()) {
            return null;
        }
        var decompositionCoeffs = new ArrayList<MultivariatePolynomial<BigInteger>>();
        for (int i = 0; i < generators.size(); ++i) {
            var coeff = MultivariatePolynomial.zero(poly.nVariables, poly.ring, poly.ordering);
            for (int j = 0; j < divResult.length - 1; ++j) {
               coeff = coeff.clone().add(groebnerBasisCoeffs.get(groebnerBasis.get(j)).get(i).clone().multiply((MultivariatePolynomial<BigInteger>) divResult[j]));
            }
            decompositionCoeffs.add(coeff);
        }
        return decompositionCoeffs;
    }
}
