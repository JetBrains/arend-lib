package org.arend.lib.util.algorithms.groebner;

import cc.redberry.rings.poly.multivar.*;
import org.apache.commons.math3.util.Pair;

import java.math.BigInteger;
import java.util.*;

public class Buchberger {

    @SuppressWarnings("unchecked")
    public Map<MultivariatePolynomial<BigInteger>, List<MultivariatePolynomial<BigInteger>>> computeGBwCoefficients(List<MultivariatePolynomial<BigInteger>> generators) {
        List<MultivariatePolynomial<BigInteger>> groebnerBasis = new ArrayList<>(generators);
        Queue<Pair<Integer, Integer>> pairsToProcess = new LinkedList<>();
        Map<MultivariatePolynomial<BigInteger>, List<MultivariatePolynomial<BigInteger>>> gbCoefficients = new HashMap<>();

        for (int i = 0; i < generators.size(); ++i) {
            for (int j = i + 1; j < generators.size(); ++j) {
                pairsToProcess.add(new Pair<>(i, j));
            }
        }

        while (!pairsToProcess.isEmpty()) {
            var pair = pairsToProcess.poll();
            var f1 = groebnerBasis.get(pair.getFirst());
            var f2 = groebnerBasis.get(pair.getSecond());
            Monomial<BigInteger> lt1 = f1.lt(), lt2 = f2.lt(), lcm = lcm(lt1, lt2);
            var s12 = f1.multiply(lcm.divideOrNull(lt1)).subtract(f2.multiply(lcm.divideOrNull(lt2)));
            var divResult = MultivariateDivision.divideAndRemainder(s12, groebnerBasis.toArray(new MultivariatePolynomial[0]));

            s12 = divResult[groebnerBasis.size()];
            if (!s12.equals(MultivariatePolynomial.zero(s12.nVariables, s12.ring, s12.ordering))) {
                var coeffs = Arrays.copyOf(divResult, divResult.length - 1);
                for (int i = 0; i < coeffs.length; ++i) {
                    coeffs[i] = coeffs[i].multiply(new MultivariatePolynomial<BigInteger>())
                }
                for (int i = 0; i < groebnerBasis.size(); ++i) {
                    pairsToProcess.add(new Pair<>(i, groebnerBasis.size()));
                }
                groebnerBasis.add(s12);
            }
        }
    }



    private Monomial<BigInteger> lcm(Monomial<BigInteger> t1, Monomial<BigInteger> t2) {
        int N = t1.exponents.length;
        int[] dv1 = Arrays.copyOf(t1.exponents, N), dv2 = t2.dv().exponents;
        for (int i = 0; i < dv1.length; ++i) {
            dv1[i] = Math.max(dv1[i], dv2[i]);
        }
        return new Monomial<>(dv1, BigInteger.ONE);
    }
}
