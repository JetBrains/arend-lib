package org.arend.lib.util.algorithms.groebner;

import cc.redberry.rings.poly.multivar.DegreeVector;
import org.apache.commons.math3.util.Pair;
import org.arend.lib.util.algorithms.polynomials.Monomial;
import org.arend.lib.util.algorithms.polynomials.Poly;
import org.arend.lib.util.algorithms.polynomials.Ring;

import java.math.BigInteger;
import java.util.*;

public class Buchberger implements GroebnerBasisAlgorithm {

    @Override
    public Map<Poly<BigInteger>, List<Poly<BigInteger>>> computeGBwCoefficients(List<Poly<BigInteger>> generators) {
        if (generators.isEmpty()) {
            return new HashMap<Poly<BigInteger>, List<Poly<BigInteger>>>(Collections.EMPTY_MAP);
        }

        List<Poly<BigInteger>> groebnerBasis = new ArrayList<>(generators);
        Queue<Pair<Integer, Integer>> pairsToProcess = new LinkedList<>();
        Map<Poly<BigInteger>, List<Poly<BigInteger>>> gbCoefficients = new HashMap<>();
        int nVars = generators.get(0).numVars();
        Ring<BigInteger> ring = generators.get(0).ring();

        for (int i = 0; i < generators.size(); ++i) {
            for (int j = i + 1; j < generators.size(); ++j) {
                pairsToProcess.add(new Pair<>(i, j));
            }
            var coeffs = new ArrayList<Poly<BigInteger>>();
            for (int j = 0; j < generators.size(); ++j) {
                if (j == i) {
                    coeffs.add(Poly.constant(BigInteger.ONE, nVars, ring));
                } else {
                    coeffs.add(Poly.constant(BigInteger.ZERO, nVars, ring));
                }
            }
            gbCoefficients.put(generators.get(i), coeffs);
        }

        while (!pairsToProcess.isEmpty()) {
            var pair = pairsToProcess.poll();
            var f1 = groebnerBasis.get(pair.getFirst());
            var f2 = groebnerBasis.get(pair.getSecond());
            Monomial<BigInteger> lt1 = f1.leadingTerm(), lt2 = f2.leadingTerm(), lcm = lt1.lcm(lt2);
            var s12 = f1.mul(lcm.divideBy(lt1)).subtr(f2.mul(lcm.divideBy(lt2)));
            Poly<BigInteger> lastRedS12 = Poly.constant(ring.zero(), nVars, ring);
            var coeffs = new ArrayList<Poly<BigInteger>>();

            for (int i = 0; i < generators.size(); ++i) {
                coeffs.add(Poly.constant(ring.zero(), nVars, ring));
            }

            while (!s12.equals(lastRedS12)) {
                var divResult = s12.divideWRemainder(groebnerBasis);

                s12 = divResult.get(groebnerBasis.size());
                if (!s12.isZero()) {
                    var newCoeffs = divResult.subList(0, divResult.size() - 1);
                    for (int i = 0; i < newCoeffs.size(); ++i) {
                        var coeff = newCoeffs.get(i).mul(Poly.constant(Ring.negUnit(ring), nVars, ring));
                        //coeffs[i] = MultivariatePolynomial.zero(nVars, ring, ordering).subtract(coeffs[i]);
                        coeffs.set(i, coeff.add(coeffs.get(i)));
                    }
                    lastRedS12 = s12;
                } else {
                    break;
                }
            }

            if (!s12.isZero()) {
                var c1 = coeffs.get(pair.getFirst()).add(new Poly<>(Collections.singletonList(lcm.divideBy(lt1))));
                coeffs.set(pair.getFirst(), c1);
                var c2 = coeffs.get(pair.getSecond()).subtr(new Poly<>(Collections.singletonList(lcm.divideBy(lt2))));
                coeffs.set(pair.getSecond(), c2);
                gbCoefficients.put(s12, coeffs);
                for (int i = 0; i < groebnerBasis.size(); ++i) {
                    pairsToProcess.add(new Pair<>(i, groebnerBasis.size()));
                }
                groebnerBasis.add(s12);
            }
        }

        return gbCoefficients;
    }
}
