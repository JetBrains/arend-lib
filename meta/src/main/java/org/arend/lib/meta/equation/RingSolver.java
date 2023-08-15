package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.error.EquationSolverError;
import org.arend.lib.meta.closure.CongruenceClosure;
import org.arend.lib.meta.cong.CongruenceMeta;
import org.arend.lib.meta.equation.datafactory.RingDataFactory;
import org.arend.lib.ring.Monomial;
import org.arend.lib.util.CountingSort;
import org.arend.lib.util.Utils;
import org.arend.lib.util.algorithms.ComMonoidWP;
import org.arend.lib.util.algorithms.groebner.Buchberger;
import org.arend.lib.util.algorithms.idealmem.GroebnerIM;
import org.arend.lib.util.algorithms.polynomials.Poly;
import org.arend.lib.util.algorithms.polynomials.Ring;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.math.BigInteger;
import java.util.*;
import java.util.stream.Collectors;

import static java.util.Collections.singletonList;

public class RingSolver extends BaseEqualitySolver {
  private final boolean isCommutative;
  private final TermCompiler termCompiler;
  private TermCompiler.CompiledTerm lastCompiled;
  private TypedExpression lastTerm;

  protected RingSolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr, CoreFunCallExpression equality, TypedExpression instance, CoreClassCallExpression classCall, CoreClassDefinition forcedClass, boolean useHypotheses) {
    super(meta, typechecker, factory, refExpr, instance, useHypotheses);
    this.equality = equality;
    termCompiler = new TermCompiler(classCall, instance, meta.ext, typechecker, refExpr, values, forcedClass);
    isCommutative = termCompiler.isLattice || classCall.getDefinition().isSubClassOf(meta.CMonoid) && (forcedClass == null || forcedClass.isSubClassOf(meta.CMonoid));
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    RingDataFactory dataFactory = new RingDataFactory(meta, dataRef, values, factory, instance, termCompiler.isLattice, termCompiler.isRing, isCommutative);
    return typechecker.typecheck(dataFactory.wrapWithData(result), null);
  }

  private void typeToRule(CoreBinding binding, List<Equality> rules) {
    if (binding == null) return;
    CoreFunCallExpression eq = Utils.toEquality(binding.getTypeExpr(), null, null);
    if (eq == null || !typechecker.compare(eq.getDefCallArguments().get(0), getValuesType(), CMP.EQ, refExpr, false, true, false)) return;
    TermCompiler.CompiledTerm lhsTerm = termCompiler.compileTerm(eq.getDefCallArguments().get(1));
    TermCompiler.CompiledTerm rhsTerm = termCompiler.compileTerm(eq.getDefCallArguments().get(2));
    if (isCommutative) {
      toCommutativeNF(lhsTerm.nf);
      toCommutativeNF(rhsTerm.nf);
    }
    rules.add(new Equality(binding, factory.ref(binding), lhsTerm, rhsTerm));
  }

  private void toCommutativeNF(List<Monomial> nf) {
    nf.replaceAll(monomial -> new Monomial(monomial.coefficient, CountingSort.sort(monomial.elements)));
  }

  private ConcreteExpression nfToRingTerm(List<Monomial> nf) {
    if (nf.isEmpty()) return factory.ref(meta.zroTerm.getRef());
    var monomialTerms = new ArrayList<ConcreteExpression>();
    for (Monomial m : nf) {
      var isNegative = m.coefficient.signum() == -1;
      var mTerm = factory.app(factory.ref(meta.coefTerm.getRef()), true, Collections.singletonList(factory.number(m.coefficient.abs())));
      if(isNegative) {
        mTerm = factory.app(factory.ref(meta.negativeTerm.getRef()), true, Collections.singletonList(mTerm));
      }

      for (Integer v : m.elements) {
        var varTerm = factory.app(factory.ref(meta.varTerm.getRef()), true, singletonList(factory.number(v)));
        mTerm = factory.app(factory.ref(meta.mulTerm.getRef()), true, Arrays.asList(mTerm, varTerm));
      }
      monomialTerms.add(mTerm);
    }
    var resTerm = monomialTerms.get(0);
    for (int i = 1; i < nf.size(); ++i) {
      resTerm = factory.app(factory.ref(meta.addTerm.getRef()), true, Arrays.asList(resTerm, monomialTerms.get(i)));
    }
    return resTerm;
  }

  @Override
  public ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter) {
    TermCompiler.CompiledTerm term1 = lastTerm == leftExpr ? lastCompiled : termCompiler.compileTerm(leftExpr.getExpression());
    TermCompiler.CompiledTerm term2 = termCompiler.compileTerm(rightExpr.getExpression());
    lastTerm = rightExpr;
    lastCompiled = term2;

    if (isCommutative) {
      toCommutativeNF(term1.nf);
      toCommutativeNF(term2.nf);
    }

    List<Monomial> nf1 = term1.nf;
    List<Monomial> nf2 = term2.nf;
    if (termCompiler.isLattice) {
      removeDuplicates(nf1);
      removeDuplicates(nf2);
      nf1 = latticeCollapse(nf1);
      nf2 = latticeCollapse(nf2);
    }
    Collections.sort(nf1);
    Collections.sort(nf2);

    if (isCommutative && useHypotheses) {
      var rules = new ArrayList<Equality>();
      ContextHelper helper = new ContextHelper(hint);
      for (CoreBinding binding : helper.getAllBindings(typechecker)) {
        typeToRule(binding, rules);
      }

      if(!rules.isEmpty()) {
        ComRingSolver comSolver = new ComRingSolver();
        ConcreteExpression result = comSolver.solve(term1, term2, rules);
        if (result == null) {
          errorReporter.report(new EquationSolverError("Ring solver failed", nf1, nf2, values.getValues(), equalitiesToAssumptions(rules), hint != null ? hint : refExpr));
        }
        return result;
      }
    }
    if (!termCompiler.isLattice) {
      nf1 = Monomial.collapse(nf1);
      nf2 = Monomial.collapse(nf2);
    }
    if (!nf1.equals(nf2)) {
      errorReporter.report(new EquationSolverError("Ring solver failed", nf1, nf2, values.getValues(), Collections.emptyList(), hint != null ? hint : refExpr));
      return null;
    }

    return factory.appBuilder(factory.ref((termCompiler.isLattice ? meta.latticeTermsEq : (termCompiler.isRing ? (isCommutative ? meta.commRingTermsEq : meta.ringTermsEq) : (isCommutative ? meta.commSemiringTermsEq : meta.ringTermsEq))).getRef()))
      .app(factory.ref(dataRef), false)
      .app(term1.concrete)
      .app(term2.concrete)
      .app(factory.ref(meta.ext.prelude.getIdp().getRef()))
      .build();
  }

  private static void removeDuplicates(List<Monomial> list) {
    list.replaceAll(monomial -> new Monomial(monomial.coefficient, MonoidSolver.removeDuplicates(monomial.elements)));
  }

  private static List<Monomial> latticeCollapse(List<Monomial> list) {
    List<Monomial> result = new ArrayList<>(list.size());
    for (Monomial m : list) {
      insert(m, result);
    }
    return result;
  }

  private static void insert(Monomial m, List<Monomial> list) {
    for (int i = 0; i < list.size(); i++) {
      Monomial.ComparisonResult result = m.compare(list.get(i));
      if (result != Monomial.ComparisonResult.UNCOMPARABLE) {
        if (result == Monomial.ComparisonResult.LESS) {
          list.set(i, m);
        }
        return;
      }
    }
    list.add(m);
  }

  private static class Equality {
    final CoreBinding binding;
    final ConcreteExpression bindingExpr;
    TermCompiler.CompiledTerm lhsTerm;
    TermCompiler.CompiledTerm rhsTerm;

    Equality(CoreBinding binding, ConcreteExpression bindingExpr, TermCompiler.CompiledTerm lhsTerm, TermCompiler.CompiledTerm rhsTerm) {
      this.binding = binding;
      this.bindingExpr = bindingExpr;
      this.lhsTerm = lhsTerm;
      this.rhsTerm = rhsTerm;
    }
  }

  private static List<EquationSolverError.Assumption> equalitiesToAssumptions(List<Equality> equalities) {
    List<EquationSolverError.Assumption> result = new ArrayList<>(equalities.size());
    for (Equality equality : equalities) {
      result.add(new EquationSolverError.Assumption(null, equality.binding, false, equality.lhsTerm.nf, equality.rhsTerm.nf));
    }
    return result;
  }

  private class ComRingSolver {

    private Poly<BigInteger> termToPoly(TermCompiler.CompiledTerm term, int numVars) {
      var poly = Poly.constant(BigInteger.ZERO, numVars, Ring.Z);

      for (Monomial m : term.nf) {
        poly = poly.add(new org.arend.lib.util.algorithms.polynomials.Monomial<>(m.coefficient, ComMonoidWP.elemsSeqToPowersSeq(m.elements, numVars), Ring.Z));
      }
      return poly;
    }

    private List<Monomial> polyToNF(Poly<BigInteger> poly) {
      var nf =  poly.monomials.stream().map(m -> new Monomial(m.coefficient, ComMonoidWP.powersSeqToElemsSeq(m.degreeVector))).collect(Collectors.toList());
      if (nf.size() > 1 && nf.get(0).elements.isEmpty() && nf.get(0).coefficient.equals(BigInteger.ZERO)) {
        nf.remove(0);
      }
      return nf;
    }

    private ConcreteExpression idealGenDecompRingTerm(List<Poly<BigInteger>> coeffs, List<ConcreteExpression> axiomsRT) {
      var summands = new ArrayList<ConcreteExpression>();
      for (int i = 0; i < coeffs.size(); ++i) {
        var coeffTerm = nfToRingTerm(polyToNF(coeffs.get(i)));
        coeffTerm = factory.app(factory.ref(meta.mulTerm.getRef()), true, Arrays.asList(coeffTerm, axiomsRT.get(i)));
        summands.add(coeffTerm);
      }

      ConcreteExpression resTerm = factory.ref(meta.zroTerm.getRef());
      for (int i = summands.size() - 1; i >= 0; --i) {
        resTerm = factory.app(factory.ref(meta.addTerm.getRef()), true, Arrays.asList(summands.get(i), resTerm));
      }
      return resTerm;
    }

    private ConcreteExpression argIsZeroToProdIsZero(ConcreteExpression a, ConcreteExpression bEqZeroPrf) {
      var prodCongProof = CongruenceMeta.applyCongruence(typechecker,
        Arrays.asList(new CongruenceClosure.EqProofOrElement(factory.ref(meta.mul.getRef()), true),
          new CongruenceClosure.EqProofOrElement(a, true),
          new CongruenceClosure.EqProofOrElement(bEqZeroPrf,  false)), factory, meta.ext.prelude);
      var aMulZeroIsZeroProof = factory.appBuilder(factory.ref(meta.zeroMulRight.getRef()))
        .app(factory.core(instance), false)
        .app(a, false)
        .build();
      return factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(prodCongProof, aMulZeroIsZeroProof));
    }

    private ConcreteExpression argsAreZeroToSumIsZero(ConcreteExpression aEqZeroPrf, ConcreteExpression bEqZeroPrf) {
      var sumCongProof = CongruenceMeta.applyCongruence(typechecker,
        Arrays.asList(new CongruenceClosure.EqProofOrElement(factory.ref(meta.plus.getRef()), true),
          new CongruenceClosure.EqProofOrElement(aEqZeroPrf, false),
          new CongruenceClosure.EqProofOrElement(bEqZeroPrf,  false)), factory, meta.ext.prelude);

      var zeroPlusZeroIsZeroProof = factory.appBuilder(factory.ref(meta.addMonZroRight.getRef()))
        .app(factory.core(instance), false)
        .app(factory.ref(meta.ext.zro.getRef()), false)
        .build();

      return factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(sumCongProof, zeroPlusZeroIsZeroProof));
    }

    // todo: implement as lemma in Arend
    private ConcreteExpression idealGenDecompEqZero(List<Poly<BigInteger>> coeffs, List<ConcreteExpression> axEqZeroProofs) {
      var summandProofs = new ArrayList<ConcreteExpression>();
      for (int i = 0; i < coeffs.size(); ++i) {
        var coeffTerm = nfToRingTerm(polyToNF(coeffs.get(i)));
        coeffTerm = factory.appBuilder(factory.ref(meta.ringInterpret.getRef()))
          .app(factory.ref(dataRef), false)
          .app(coeffTerm).build();
        summandProofs.add(argIsZeroToProdIsZero(coeffTerm, axEqZeroProofs.get(i)));
      }
      var resProof = summandProofs.get(0);
      for (int i = 1; i < summandProofs.size(); ++i) {
        resProof = argsAreZeroToSumIsZero(resProof, summandProofs.get(i));
      }
      return resProof;
    }

    private int numVarsInNF(List<Monomial> nf) {
      if (nf.isEmpty()) return 0;
      return Collections.max(nf.stream().map(m -> m.elements.isEmpty() ? 0 : Collections.max(m.elements)).toList()) + 1;
    }

    private ConcreteExpression minusRingTerm(ConcreteExpression a, ConcreteExpression b) {
      return factory.appBuilder(factory.ref(meta.addTerm.getRef()))
        .app(a, true)
        .app(factory.app(factory.ref(meta.negativeTerm.getRef()), true, Collections.singletonList(b)), true)
        .build();
    }

    private ConcreteExpression minusRingElement(ConcreteExpression a, ConcreteExpression b) {
      return factory.appBuilder(factory.ref(meta.plus.getRef()))
        .app(a, true)
        .app(factory.app(factory.ref(meta.negative.getRef()), true, Collections.singletonList(b)), true)
        .build();
    }

    public ConcreteExpression solve(TermCompiler.CompiledTerm term1, TermCompiler.CompiledTerm term2, List<Equality> axioms) {
      int numVariables = Integer.max(numVarsInNF(term1.nf), numVarsInNF(term2.nf));
      for (Equality axiom : axioms) {
        numVariables = Integer.max(numVarsInNF(axiom.lhsTerm.nf), numVariables);
        numVariables = Integer.max(numVarsInNF(axiom.rhsTerm.nf), numVariables);
      }

      var p = termToPoly(term1, numVariables).subtr(termToPoly(term2, numVariables));
      var idealGen = new ArrayList<Poly<BigInteger>>();

      for (Equality axiom : axioms) {
        idealGen.add(termToPoly(axiom.lhsTerm, numVariables).subtr(termToPoly(axiom.rhsTerm, numVariables)));
      }

      var idealCoeffs = new GroebnerIM(new Buchberger()).computeGenDecomposition(p, idealGen);

      if (idealCoeffs == null) {
        return null;
      }

      var genCoeffs = new ArrayList<ConcreteExpression>();
      var axiomDiffs = new ArrayList<ConcreteExpression>();

      for (int i = 0;i < axioms.size(); ++i) {
        var axiom = axioms.get(i);
        var axiomDiff = minusRingElement(axiom.lhsTerm.originalExpr, axiom.rhsTerm.originalExpr);
        var axDiffIsZero = factory.appBuilder(factory.ref(meta.toZero.getRef()))
          .app(factory.core(instance), false)
          .app(axiom.lhsTerm.originalExpr, false)
          .app(axiom.rhsTerm.originalExpr, false)
          .app(axiom.bindingExpr)
          .build();
        var coeffTerm = nfToRingTerm(polyToNF(idealCoeffs.get(i)));

        coeffTerm = factory.appBuilder(factory.ref(meta.ringInterpret.getRef()))
          .app(factory.ref(dataRef), false)
          .app(coeffTerm).build();
        axiomDiffs.add(minusRingTerm(axiom.lhsTerm.concrete, axiom.rhsTerm.concrete));
        genCoeffs.add(factory.tuple(coeffTerm, axiomDiff, axDiffIsZero));
      }

      /*
      var axDiffIsZeroPrf = new ArrayList<ConcreteExpression>();

      for (Equality axiom : axioms) {
        axiomDiffs.add(minusRingTerm(axiom.lhsTerm.concrete, axiom.rhsTerm.concrete));
        axDiffIsZeroPrf.add(factory.appBuilder(factory.ref(meta.toZero.getRef()))
                .app(factory.core(instance), false)
                .app(axiom.lhsTerm.originalExpr)
                .app(axiom.rhsTerm.originalExpr)
                .app(axiom.binding)
                .build());
      }

       */

      // term1 - term2 = sum_i idealCoeffs(i) * (axiom(i).L - axiom(i).R)
      var decompositionProof = factory.appBuilder(factory.ref(meta.commRingTermsEq.getRef()))
        .app(factory.ref(dataRef), false)
        .app(minusRingTerm(term1.concrete, term2.concrete))
        .app(idealGenDecompRingTerm(idealCoeffs, axiomDiffs))
        .app(factory.ref(meta.ext.prelude.getIdp().getRef()))
        .build();

      /*
      // term1 - term2 = 0
      var isZeroProof = factory.appBuilder(factory.ref(meta.ext.concat.getRef()))
              .app(decompositionProof)
              .app(idealGenDecompEqZero(idealCoeffs, axDiffIsZeroPrf))
              .build();

       */

      // sum_i idealCoeffs(i) * (axiom(i).L - axiom(i).R) = 0
      var idealGenDecompEqZero = factory.appBuilder(factory.ref(meta.gensZeroToIdealZero.getRef()))
        .app(MonoidSolver.formList(genCoeffs, factory, meta.ext.nil, meta.ext.cons))
        .build();

      // term1 - term2 = 0
      var isZeroProof = factory.appBuilder(factory.ref(meta.ext.concat.getRef()))
        .app(decompositionProof)
        .app(idealGenDecompEqZero)
        .build();

      return factory.appBuilder(factory.ref(meta.fromZero.getRef()))
        .app(factory.core(instance), false)
        .app(term1.originalExpr, false)
        .app(term2.originalExpr, false)
        .app(isZeroProof)
        .build();
    }
  }
}
