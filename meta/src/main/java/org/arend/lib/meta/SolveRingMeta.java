package org.arend.lib.meta;

import cc.redberry.rings.Rings;
import cc.redberry.rings.bigint.BigInteger;
import cc.redberry.rings.poly.multivar.GroebnerBases;
import cc.redberry.rings.poly.multivar.MonomialOrder;
import cc.redberry.rings.poly.multivar.MultivariatePolynomial;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.expr.*;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.Context;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

public class SolveRingMeta extends BaseMetaDefinition {
    private Values<CoreExpression> terms;

    @Dependency(module = "Algebra.Ring", name = "Ring.*") CoreClassField mul;
    @Dependency(module = "Algebra.Ring", name = "Ring.+") CoreClassField plus;
    @Dependency(module = "Algebra.Ring", name = "Ring.negative") CoreClassField neg;
    @Dependency(module = "Algebra.Ring", name = "Ring.ide") CoreClassField unit;
    @Dependency(module = "Algebra.Ring", name = "Ring.zro") CoreClassField zero;

    private String termToRingExpression(CoreExpression term) {
        if (term instanceof CoreAppExpression) {
            CoreExpression op_a1 = ((CoreAppExpression) term).getFunction();
            CoreExpression a2 = ((CoreAppExpression) term).getArgument();

            if (op_a1 instanceof CoreAppExpression) {
                CoreExpression op = ((CoreAppExpression) op_a1).getFunction();
                CoreExpression a1 = ((CoreAppExpression) op_a1).getArgument();

                if (op instanceof CoreFieldCallExpression) {
                    if (((CoreFieldCallExpression)op).getDefinition() == plus) {
                        return termToRingExpression(a1) + " + " + termToRingExpression(a2);
                    }
                    if (((CoreFieldCallExpression)op).getDefinition() == mul) {
                        return termToRingExpression(a1) + " * " + termToRingExpression(a2);
                    }
                }
            } else if (op_a1 instanceof CoreFieldCallExpression) {
                if (((CoreFieldCallExpression)op_a1).getDefinition() == neg) {
                    return "(- " + termToRingExpression(a2) + ")";
                }
            }
        } else if (term instanceof CoreFieldCallExpression) {
            if (((CoreFieldCallExpression)term).getDefinition() == unit) {
                return "1";
            }
            if (((CoreFieldCallExpression)term).getDefinition() == zero) {
                return "0";
            }
        }

        return "x" + terms.addValue(term);
    }

    private List<MultivariatePolynomial<BigInteger>> computeIdealCoefficients(String poly, List<String> gens, List<String> variables) {
        List<String> extVars = new ArrayList<>(variables);

        extVars.add(0, "t");
        extVars.add("z");

        List<String> extGens = new ArrayList<>(gens);
        int N = gens.size() + 1;
        extGens.add("1 - z * (" + poly + ")");
        for (int i = 0; i < N + 1; ++i) {
            extVars.add("e" + i);
            extGens.add("t * (" + extGens.get(i) + ")" + " - e" + i);
        }
        for (int i = 0; i < N; ++i) {
            for (int j = i; j < N; ++j) {
                extGens.add("e" + i + " * " + "e" + j);
            }
            extGens.add("e" + i + " * t");
        }

        List<MultivariatePolynomial<BigInteger>> parsedExtGens = extGens.stream().map(gen -> MultivariatePolynomial.parse(gen, extVars.toArray(new String[0]))).collect(Collectors.toList());
        List<MultivariatePolynomial<BigInteger>> gb = GroebnerBases.GroebnerBasis(parsedExtGens, MonomialOrder.GREVLEX);

        for (MultivariatePolynomial<BigInteger> gbPoly : gb) {
            var monomialIt = gbPoly.descendingIterator();
            if (monomialIt.next().exponents[0] > 0) {
                List<MultivariatePolynomial<BigInteger>> coefficients = new ArrayList<>();
                for (int i = 0; i < N; ++i) coefficients.add(MultivariatePolynomial.zero(extVars.size(), Rings.Z, MonomialOrder.GREVLEX));
                while (monomialIt.hasNext()) {
                    var monomial = monomialIt.next();
                    for (int i = 0; i < N; ++i) {
                        if (monomial.exponents[i + N + 1] > 0) {
                            var coeff = coefficients.get(i);
                            int[] exps = new int[extVars.size()];
                            exps[i + N + 1] = 1;
                            coefficients.set(i, coeff.add(monomial.divideOrNull(exps)));
                            break;
                        }
                    }
                }
                for (int i = 0; i < N; ++i) {

                }
                break;
            }
        }

        return null;
    }

    public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        CoreFunCallExpression equalityToProve = contextData.getExpectedType().toEquality();
        if (equalityToProve == null) return null;
        // CoreExpression elementsType = equalityToProve.getDefCallArguments().get(0);

        List<String> polynomials = new ArrayList<>();
        terms = new Values<>(typechecker, contextData.getReferenceExpression());

        ContextHelper contextHelper = new ContextHelper(Context.TRIVIAL, contextData.getArguments().isEmpty() ? null : contextData.getArguments().get(0).getExpression());
        for (CoreBinding binding : contextHelper.getAllBindings(typechecker)) {
            CoreFunCallExpression equality = binding.getTypeExpr().toEquality();
            if (equality != null) {
                String leftPoly = termToRingExpression(equality.getDefCallArguments().get(1));
                String rightPoly = termToRingExpression(equality.getDefCallArguments().get(2));
                polynomials.add(leftPoly + " - (" + rightPoly + ")");
            }
        }

        List<String> variables =new ArrayList<>();

        // variables.add("t");
        for (int i = 0; i < terms.getValues().size(); ++i) {
            variables.add("x" + i);
        }

        return null;
    }
}
