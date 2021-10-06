package org.arend.lib.util.algorithms;

import org.arend.ext.util.Pair;
import org.arend.lib.util.algorithms.idealmem.IdealMembership;
import org.arend.lib.util.algorithms.polynomials.Monomial;
import org.arend.lib.util.algorithms.polynomials.Poly;
import org.arend.lib.util.algorithms.polynomials.Ring;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ComMonoidWP {
  private final IdealMembership idealMembershipAlg;

  public ComMonoidWP(IdealMembership idealMembershipAlg) {
    this.idealMembershipAlg = idealMembershipAlg;
  }

  private static Monomial<BigInteger> wordToMonomial(List<Integer> word) {
    return new Monomial<>(BigInteger.ONE, word, Ring.Z);
  }

  public static List<Integer> findIndexesToRemove(List<Integer> word, List<Integer> powersToErase) {
    var powersCopy = new ArrayList<>(powersToErase);
    var indexesToRemove = new ArrayList<Integer>();

    for (int i = 0; i < word.size(); ++i) {
      int pow = powersCopy.get(word.get(i));
      if (pow > 0) {
        powersCopy.set(word.get(i), pow - 1);
        indexesToRemove.add(i - indexesToRemove.size());
      }
    }

    return indexesToRemove;
  }

  public static List<Integer> elemsSeqToPowersSeq(List<Integer> word, int alphabetSize) {
    var powersSeq = new ArrayList<Integer>();
    for (int i = 0; i < alphabetSize; ++i) {
      powersSeq.add(0);
    }

    for (int a : word) {
      powersSeq.set(a, powersSeq.get(a) + 1);
    }

    return powersSeq;
  }

  public static List<Integer> powersSeqToElemsSeq(List<Integer> powers) {
    var word = new ArrayList<Integer>();
    for (int i = 0; i < powers.size(); ++i) {
      for (int j = 0; j < powers.get(i); ++j) {
        word.add(i);
      }
    }
    return word;
  }

  private static List<Integer> monomialToWord(Monomial<BigInteger> monomial) {
    return monomial.degreeVector;
  }

  private static Poly<BigInteger> twoMonomialsToBinomial(Monomial<BigInteger> t1, Monomial<BigInteger> t2) {
    var binomial = new Poly<>(Collections.singletonList(t2)); // MultivariatePolynomial.create(t1.exponents.length, Rings.Z, MonomialOrder.GREVLEX, t2);

    return binomial.subtr(new Poly<>(Collections.singletonList(t1)));
  }

  private static class ReductionStep {
    public Monomial<BigInteger> redex = null;
    public Integer axiomInd = -1;
    public boolean isDirectApp = true;
  }

  private static ReductionStep applyReduction(Monomial<BigInteger> t, List<Poly<BigInteger>> coeffs,
                                              List<Pair<List<Integer>, List<Integer>>> axioms) {
    var reductionStep = new ReductionStep();
    for (int i = 0; i < coeffs.size(); ++i) {
      for (Monomial<BigInteger> tQ : coeffs.get(i).monomials) {
        var f1 = wordToMonomial(axioms.get(i).proj1);
        var f2 = wordToMonomial(axioms.get(i).proj2);
        if (tQ.coefficient.compareTo(BigInteger.ZERO) >= 0) {
          if (f1.mul(tQ.degreeVector).degreeVector.equals(t.degreeVector)) {
            reductionStep.redex = f2.mul(tQ.degreeVector);
            reductionStep.axiomInd = i;
            coeffs.set(i, coeffs.get(i).subtr(wordToMonomial(monomialToWord(tQ))));
            return reductionStep;
          }
        } else if (f2.mul(tQ.degreeVector).degreeVector.equals(t.degreeVector)) {
          reductionStep.redex = f1.mul(tQ.degreeVector);
          reductionStep.axiomInd = i;
          reductionStep.isDirectApp = false;
          coeffs.set(i, coeffs.get(i).add(wordToMonomial(monomialToWord(tQ))));
          return reductionStep;
        }
      }
    }
    return null;
  }

  public List<Pair<Integer, Boolean>> solve(List<Integer> word1, List<Integer> word2, List<Pair<List<Integer>, List<Integer>>> axioms) {
    var t1 = wordToMonomial(word1);
    var t2 = wordToMonomial(word2);
    var wpPoly = twoMonomialsToBinomial(t1, t2);
    List<Poly<BigInteger>> axiomPolys = new ArrayList<>();

    for (Pair<List<Integer>, List<Integer>> axiom : axioms) {
      axiomPolys.add(twoMonomialsToBinomial(wordToMonomial(axiom.proj1), wordToMonomial(axiom.proj2)));
    }

    var decompCoeffs = idealMembershipAlg.computeGenDecomposition(wpPoly, axiomPolys);

    if (decompCoeffs == null) {
      return null;
    }

    List<Pair<Integer, Boolean>> reductionSteps = new ArrayList<>();
    var curRedex = t1;

    while (true) {
      var reductionStep = applyReduction(curRedex, decompCoeffs, axioms);
      if (reductionStep == null) return null;

      reductionSteps.add(new Pair<>(reductionStep.axiomInd, reductionStep.isDirectApp));
      if (reductionStep.redex.degreeVector.equals(t2.degreeVector)) {
        break;
      }
      curRedex = reductionStep.redex;
    }

    return reductionSteps;
  }
}
