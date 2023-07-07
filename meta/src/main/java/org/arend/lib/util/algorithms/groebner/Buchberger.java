package org.arend.lib.util.algorithms.groebner;

import org.arend.ext.util.Pair;
import org.arend.lib.util.algorithms.polynomials.Monomial;
import org.arend.lib.util.algorithms.polynomials.Poly;
import org.arend.lib.util.algorithms.polynomials.Ring;

import java.math.BigInteger;
import java.util.*;
import java.util.stream.Collectors;

public class Buchberger implements GroebnerBasisAlgorithm {

  @Override
  public Map<Poly<BigInteger>, List<Poly<BigInteger>>> computeGBwCoefficients(List<Poly<BigInteger>> generators) {
    if (generators.isEmpty()) {
      return new HashMap<>();
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
      var f1 = groebnerBasis.get(pair.proj1);
      var f2 = groebnerBasis.get(pair.proj2);
      Monomial<BigInteger> lt1 = f1.leadingTerm(), lt2 = f2.leadingTerm(), lcm = lt1.lcm(lt2);
      var s12 = f1.mul(lcm.divideBy(lt1)).subtr(f2.mul(lcm.divideBy(lt2)));
      Poly<BigInteger> lastRedS12 = Poly.constant(ring.zero(), nVars, ring);
      var coeffs = new ArrayList<Poly<BigInteger>>();

      for (int i = 0; i < generators.size(); ++i) {
        var c1 = gbCoefficients.get(groebnerBasis.get(pair.proj1)).get(i).mul(new Poly<>(Collections.singletonList(lcm.divideBy(lt1))));
        var c2 = gbCoefficients.get(groebnerBasis.get(pair.proj2)).get(i).mul(new Poly<>(Collections.singletonList(lcm.divideBy(lt2))));
        // mul(Poly.constant(Ring.negUnit(ring), nVars, ring));
        coeffs.add(c1.subtr(c2));
      }

      var divResult = s12.divideWRemainder(groebnerBasis);

      s12 = divResult.get(groebnerBasis.size());
      if (!s12.isZero()) {
        var groebnerCoeffs = divResult.subList(0, divResult.size() - 1);
        for (int i = 0; i < generators.size(); ++i) {
          for (int j = 0; j < groebnerBasis.size(); ++j) {
            var coeff = groebnerCoeffs.get(j).mul(Poly.constant(Ring.negUnit(ring), nVars, ring)).
                    mul(gbCoefficients.get(groebnerBasis.get(j)).get(i));
            coeffs.set(i, coeff.add(coeffs.get(i)));
          }
        }
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
