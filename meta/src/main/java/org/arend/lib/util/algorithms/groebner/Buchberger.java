package org.arend.lib.util.algorithms.groebner;

import cc.redberry.rings.Ring;
import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.multivar.*;
import org.apache.commons.math3.util.Pair;

import java.util.*;

public class Buchberger implements GroebnerBasisAlgorithm {

    @Override
    @SuppressWarnings("unchecked")
    public Map<MultivariatePolynomial<BigInteger>, List<MultivariatePolynomial<BigInteger>>> computeGBwCoefficients(List<MultivariatePolynomial<BigInteger>> generators) {
        if (generators.isEmpty()) {
            return new HashMap<MultivariatePolynomial<BigInteger>, List<MultivariatePolynomial<BigInteger>>>(Collections.EMPTY_MAP);
        }

        List<MultivariatePolynomial<BigInteger>> groebnerBasis = new ArrayList<>(generators);
        Queue<Pair<Integer, Integer>> pairsToProcess = new LinkedList<>();
        Map<MultivariatePolynomial<BigInteger>, List<MultivariatePolynomial<BigInteger>>> gbCoefficients = new HashMap<>();
        int nVars = generators.get(0).nVariables;
        Ring<BigInteger> ring = generators.get(0).ring;
        Comparator<DegreeVector> ordering = generators.get(0).ordering;

        for (int i = 0; i < generators.size(); ++i) {
            for (int j = i + 1; j < generators.size(); ++j) {
                pairsToProcess.add(new Pair<>(i, j));
            }
            var coeffs = new ArrayList<MultivariatePolynomial<BigInteger>>();
            for (int j = 0; j < generators.size(); ++j) {
                if (j == i) {
                    coeffs.add(MultivariatePolynomial.one(nVars, ring, ordering));
                } else {
                    coeffs.add(MultivariatePolynomial.zero(nVars, ring, ordering));
                }
            }
            gbCoefficients.put(generators.get(i), coeffs);
        }

        while (!pairsToProcess.isEmpty()) {
            var pair = pairsToProcess.poll();
            var f1 = groebnerBasis.get(pair.getFirst()).clone();
            var f2 = groebnerBasis.get(pair.getSecond()).clone();
            Monomial<BigInteger> lt1 = f1.lt(), lt2 = f2.lt(), lcm = lcm(lt1, lt2);
            var s12 = f1.multiply(lcm.divideOrNull(lt1)).subtract(f2.multiply(lcm.divideOrNull(lt2)));
            var divResult = MultivariateDivision.divideAndRemainder(s12, groebnerBasis.toArray(new MultivariatePolynomial[0]));

            s12 = divResult[groebnerBasis.size()];
            if (!s12.equals(MultivariatePolynomial.zero(nVars, ring, ordering))) {
                var coeffs = Arrays.copyOf(divResult, divResult.length - 1);
                for (int i = 0; i < coeffs.length; ++i) {
                    coeffs[i] = MultivariatePolynomial.zero(nVars, ring, ordering).subtract(coeffs[i]);
                }
                coeffs[pair.getFirst()] = (MultivariatePolynomial<BigInteger>) coeffs[pair.getFirst()].clone().add(lcm.divideOrNull(lt1));
                coeffs[pair.getSecond()] = (MultivariatePolynomial<BigInteger>) coeffs[pair.getSecond()].clone().subtract(lcm.divideOrNull(lt2));
                gbCoefficients.put(s12, Arrays.asList(coeffs));
                for (int i = 0; i < groebnerBasis.size(); ++i) {
                    pairsToProcess.add(new Pair<>(i, groebnerBasis.size()));
                }
                groebnerBasis.add(s12);
            }
        }

        return gbCoefficients;
    }

    private static Monomial<BigInteger> lcm(Monomial<BigInteger> t1, Monomial<BigInteger> t2) {
        int N = t1.exponents.length;
        int[] dv1 = Arrays.copyOf(t1.exponents, N), dv2 = t2.dv().exponents;
        for (int i = 0; i < dv1.length; ++i) {
            dv1[i] = Math.max(dv1[i], dv2[i]);
        }
        return new Monomial<>(dv1, BigInteger.ONE);
    }
}
