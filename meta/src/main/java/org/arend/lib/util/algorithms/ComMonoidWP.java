package org.arend.lib.util.algorithms;

import cc.redberry.rings.Rings;
import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.multivar.Monomial;
import cc.redberry.rings.poly.multivar.MonomialOrder;
import cc.redberry.rings.poly.multivar.MultivariatePolynomial;
import org.arend.lib.util.Pair;
import org.arend.lib.util.algorithms.idealmem.IdealMembership;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class ComMonoidWP {
    private final IdealMembership idealMembershipAlg;

    public ComMonoidWP(IdealMembership idealMembershipAlg) {
        this.idealMembershipAlg = idealMembershipAlg;
    }

    private static Monomial<BigInteger> wordToMonomial(List<Integer> word) {
        int[] degrees = new int[word.size()];
        for (int i = 0; i < word.size(); ++i) {
            degrees[i] = word.get(i);
        }
        return new Monomial<>(degrees, BigInteger.ONE);
    }

    private static List<Integer> monomialToWord(Monomial<BigInteger> monomial) {
        var word = new ArrayList<Integer>();
        for (int i = 0; i < monomial.exponents.length; ++i) {
            word.add(monomial.exponents[i]);
        }
        return word;
    }

    @SuppressWarnings("unchecked")
    private static MultivariatePolynomial<BigInteger> twoMonomialsToBinomial(Monomial<BigInteger> t1, Monomial<BigInteger> t2) {
        var binomial = MultivariatePolynomial.create(t1.exponents.length, Rings.Z, MonomialOrder.GREVLEX, t2);

        binomial.subtract(t1);
        return binomial;
    }

    private static class ReductionStep {
        public Monomial<BigInteger> redex = null;
        public Integer axiomInd = -1;
        public boolean isDirectApp = true;
    }

    private static ReductionStep applyReduction(Monomial<BigInteger> t, List<MultivariatePolynomial<BigInteger>> coeffs,
                                                                      List<Pair<List<Integer>, List<Integer>>> axioms) {
        var reductionStep = new ReductionStep();
        for (int i = 0; i < coeffs.size(); ++i) {
            for (Monomial<BigInteger> tQ : coeffs.get(i)) {
                var f1 = wordToMonomial(axioms.get(i).proj1);
                var f2 = wordToMonomial(axioms.get(i).proj2);
                if (tQ.coefficient.compareTo(BigInteger.ZERO) >= 0) {
                    if (f1.multiply(tQ.exponents).dv().dvEquals(t.dv())) {
                        reductionStep.redex = f2.multiply(tQ.exponents);
                        reductionStep.axiomInd = i;
                        coeffs.set(i, coeffs.get(i).subtract(wordToMonomial(monomialToWord(tQ))));
                        return reductionStep;
                    }
                } else if (f2.multiply(tQ.exponents).dv().dvEquals(t.dv())) {
                    reductionStep.redex = f1.multiply(tQ.exponents);
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
        List<MultivariatePolynomial<BigInteger>> axiomPolys = new ArrayList<>();

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
            if (reductionStep.redex.dv().dvEquals(t2.dv())) {
                break;
            }
            curRedex = reductionStep.redex;
        }

        return reductionSteps;
    }
}
