package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteAppBuilder;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.expr.ConcreteAppExpression;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.error.MonoidSolverError;
import org.arend.lib.meta.equation.binop_matcher.DefinitionFunctionMatcher;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;
import org.arend.lib.meta.equation.datafactory.CategoryDataFactory;
import org.arend.lib.meta.equation.datafactory.DataFactory;
import org.arend.lib.meta.equation.datafactory.MonoidDataFactory;
import org.arend.lib.util.CountingSort;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;
import org.arend.lib.util.algorithms.ComMonoidWP;
import org.arend.lib.util.algorithms.groebner.Buchberger;
import org.arend.lib.util.algorithms.idealmem.GroebnerIM;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.stream.Collectors;

import static java.util.Collections.singletonList;

public class MonoidSolver extends BaseEqualitySolver {
  private final FunctionMatcher mulMatcher;
  private final FunctionMatcher ideMatcher;
  private CompiledTerm lastCompiled;
  private TypedExpression lastTerm;
  private Map<CoreBinding, List<RuleExt>> contextRules;
  private boolean isCommutative;
  private boolean isSemilattice;
  private final boolean isMultiplicative;
  private final boolean isCat;
  private final Values<CoreExpression> obValues;
  protected final List<ConcreteLetClause> letClauses;
  private final Map<Pair<Integer,Integer>, Map<Integer,Integer>> homMap; // the key is the pair (domain,codomain), the value is a map from indices in `values` to indices specific to those objects.
  private final Map<Integer, Integer> domMap; // indices of morphisms in `values` to indices of domains.
  private final Map<Integer, Integer> codomMap; // indices of morphisms in `values` to indices of codomains.

  public MonoidSolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr, CoreFunCallExpression equality, TypedExpression instance, CoreClassCallExpression classCall, CoreClassDefinition forcedClass, boolean useHypotheses) {
    super(meta, typechecker, factory, refExpr, instance, useHypotheses);
    this.equality = equality;

    letClauses = new ArrayList<>();
    isCat = classCall == null;
    isSemilattice = !isCat && classCall.getDefinition().isSubClassOf(meta.MSemilattice) && (forcedClass == null || forcedClass.isSubClassOf(meta.MSemilattice));
    isMultiplicative = !isSemilattice && !isCat && classCall.getDefinition().isSubClassOf(meta.Monoid) && (forcedClass == null || forcedClass.isSubClassOf(meta.Monoid));
    isCommutative = !isCat && (isSemilattice || isMultiplicative && classCall.getDefinition().isSubClassOf(meta.CMonoid) && (forcedClass == null || forcedClass.isSubClassOf(meta.CMonoid)) || !isMultiplicative && classCall.getDefinition().isSubClassOf(meta.AbMonoid) && (forcedClass == null || forcedClass.isSubClassOf(meta.AbMonoid)));
    CoreClassField ide = isSemilattice ? meta.top : isMultiplicative ? meta.ext.ide : meta.ext.zro;
    CoreClassField mul = isSemilattice ? meta.meet : isMultiplicative ? meta.mul : meta.plus;
    mulMatcher = isCat ? new DefinitionFunctionMatcher(meta.ext.sipMeta.catComp, 5) : FunctionMatcher.makeFieldMatcher(classCall, instance, mul, typechecker, factory, refExpr, meta.ext, 2);
    ideMatcher = isCat ? new DefinitionFunctionMatcher(meta.ext.sipMeta.catId, 1) : FunctionMatcher.makeFieldMatcher(classCall, instance, ide, typechecker, factory, refExpr, meta.ext, 0);
    obValues = isCat ? new Values<>(typechecker, refExpr) : null;
    homMap = isCat ? new HashMap<>() : null;
    domMap = isCat ? new HashMap<>() : null;
    codomMap = isCat ? new HashMap<>() : null;
  }

  public static List<Integer> removeDuplicates(List<Integer> list) {
    List<Integer> result = new ArrayList<>();
    for (int i = 0; i < list.size(); i++) {
      if (i == list.size() - 1 || !list.get(i).equals(list.get(i + 1))) {
        result.add(list.get(i));
      }
    }
    return result;
  }

  private ConcreteExpression appendRightNFProof(ConcreteExpression nf, ConcreteExpression nfPatch, ConcreteExpression oldProof) {
    if (nf == null) {
      return null;
    }

    var mul = isCat ? factory.ref(meta.catMul.getRef()) : factory.ref(meta.mul.getRef());
    var interpretNF = isCat ? factory.ref(meta.catInterpretNF.getRef()) : factory.ref(meta.monoidInterpretNF.getRef());
    var interpretNFConcat = isCat ? factory.ref(meta.catInterpretNFConcat.getRef()) : factory.ref(meta.monoidInterpretNFConcat.getRef());
    var nfConcatProof = factory.appBuilder(interpretNFConcat).app(nf).app(nfPatch).build();

    if (oldProof == null) {
      return nfConcatProof;
    }

    var nfPatchInterpreted = factory.appBuilder(interpretNF).app(nfPatch).build();
    var nfVar = factory.local("nfVar");
    var pmapLambda = factory.lam(Collections.singletonList(factory.param(nfVar)), factory.appBuilder(mul).app(factory.ref(nfVar)).app(nfPatchInterpreted).build());

    return factory.appBuilder(factory.ref(meta.ext.concat.getRef())).app(nfConcatProof).app(factory.appBuilder(factory.ref(meta.ext.pmap.getRef())).app(pmapLambda).app(oldProof).build()).build();
  }

  private Pair<List<List<Integer>>, Integer> cutAccordingToOccurrences(List<Integer> subExpr, List<Integer> expr, List<Integer> occurrences) {
    List<List<Integer>> result = new ArrayList<>();
    List<Integer> exprSuffix = new ArrayList<>(expr);
    int occurIndex = 0;
    int occurCount = 0;
    int occurPos = -1;

    for (int occ = 0; occ <= expr.size() - subExpr.size(); ++occ) {
      var tail = exprSuffix.subList(occurPos + 1, exprSuffix.size());

      occurPos = Collections.indexOfSubList(tail, subExpr);
      if (occurPos == -1) {
        break;
      }

      if (occurrences == null || occurIndex < occurrences.size() && occurrences.get(occurIndex) == occurCount) {
        if (occurPos != 0) {
          result.add(new ArrayList<>(exprSuffix.subList(0, occurPos)));
        }
        result.add(null);
        exprSuffix = new ArrayList<>(exprSuffix.subList(occurPos + subExpr.size(), exprSuffix.size()));
        occurCount = 0;
        ++occurIndex;
        occurPos = -1;
        if (occurrences != null && occurIndex == occurrences.size()) {
          break;
        }
        continue;
      }

      ++occurCount;
    }

    if (!exprSuffix.isEmpty()) {
      result.add(exprSuffix);
    }
    return new Pair<>(result, occurCount);
  }

  @Override
  public SubexprOccurrences matchSubexpr(@NotNull TypedExpression subExpr, @NotNull TypedExpression expr, @NotNull ErrorReporter errorReporter, List<Integer> occurrences) {
    if (isCommutative || isSemilattice) return super.matchSubexpr(subExpr, expr, errorReporter, occurrences);

    CompiledTerm subExTerm = compileTerm(subExpr.getExpression());
    CompiledTerm term = compileTerm(expr.getExpression());
    SubexprOccurrences result = new SubexprOccurrences();

    result.occurrenceVar = factory.local("occurVar");
    result.subExprMissed = term.nf.size() == 1 && (expr.getExpression() instanceof CoreAppExpression);

    if (term.nf.isEmpty()) {
      if (!subExTerm.nf.isEmpty()) {
        result.occurrenceVar = null;
        return result;
      }
      return super.matchSubexpr(subExpr, expr, errorReporter, occurrences);
    }

    if (subExTerm.nf.isEmpty()) {
      result.occurrenceVar = null;
      return result;
    }

    // Now this check is not needed, but keep it for the future
    if (!isCommutative) {
      var exprSplitting = cutAccordingToOccurrences(subExTerm.nf, term.nf, occurrences);
      var pieces = exprSplitting.proj1;

      result.numOccurrencesSkipped = exprSplitting.proj2;

      if (pieces.size() == 1 && pieces.get(0) != null) {
        result.occurrenceVar = null;
        return result;
      }

      for (List<Integer> piece : pieces) {
        if (piece == null) {
          ++result.numOccurrences;
        }
      }

      var mul = isCat ? factory.ref(meta.catMul.getRef()) : factory.ref(meta.mul.getRef());
      var interpretNF = isCat ? factory.ref(meta.catInterpretNF.getRef()) : factory.ref(meta.monoidInterpretNF.getRef());
      var subExprNF = computeNFTerm(subExTerm.nf);
      var constructedExprNF = pieces.get(0) == null ? new ArrayList<>(subExTerm.nf) : new ArrayList<>(pieces.get(0));
      ConcreteExpression concatNFsProof = null;

      result.exprWithOccurrences = pieces.get(0) == null ? factory.ref(result.occurrenceVar) : factory.app(interpretNF, true, computeNFTerm(pieces.get(0)));

      for (int i = 1; i < pieces.size(); ++i) {
        var piece = pieces.get(i);
        var pieceNFTerm = piece == null ? subExprNF : computeNFTerm(piece);
        var pieceTerm = piece == null ? factory.ref(result.occurrenceVar) : factory.app(interpretNF, true, pieceNFTerm);
        var pieceTermSubExpr = piece == null ? factory.core(subExpr) : factory.app(interpretNF, true, pieceNFTerm);
        result.exprWithOccurrences = factory.appBuilder(mul).app(result.exprWithOccurrences).app(pieceTerm).build();
        concatNFsProof = appendRightNFProof(computeNFTerm(constructedExprNF), pieceNFTerm, concatNFsProof);
        if (piece == null) constructedExprNF.addAll(subExTerm.nf); else constructedExprNF.addAll(piece);
      }

      var normConsist = isCat ? meta.catNormConsist.getRef() : meta.monoidNormConsist.getRef();

      ConcreteExpression normConsistSubExpr;
      ConcreteExpression normConsistExpr;

      if (!isCat) {
        normConsistSubExpr = factory.appBuilder(factory.ref(normConsist)).app(subExTerm.concrete).build();
        normConsistExpr = factory.appBuilder(factory.ref(normConsist)).app(term.concrete).build();
      } else {
        int subExprDom = domMap.get(subExTerm.nf.get(subExTerm.nf.size() - 1));
        int subExprCod = codomMap.get(subExTerm.nf.get(0));
        int exprDom = domMap.get(term.nf.get(term.nf.size() - 1));
        int exprCod = codomMap.get(term.nf.get(0));
        normConsistSubExpr = factory.appBuilder(factory.ref(normConsist))
                .app(factory.ref(dataRef), false)
                .app(factory.number(subExprDom), false).app(factory.number(subExprCod), false)
                .app(subExTerm.concrete).build();
        normConsistExpr = factory.appBuilder(factory.ref(normConsist))
                .app(factory.hole(), false)
                .app(factory.number(exprDom), false).app(factory.number(exprCod), false)
                .app(term.concrete).build();
      }

      var occLambda = factory.lam(Collections.singletonList(factory.param(result.occurrenceVar)), result.exprWithOccurrences);
              // factory.lam(Collections.singletonList(factory.param(Collections.singletonList(result.occurrenceVar), factory.core(subExpr.getType().computeTyped()))), result.exprWithOccurrences);
      var pmapOccurrence = factory.appBuilder(factory.ref(meta.ext.pmap.getRef()))
              .app(occLambda).app(factory.appBuilder(factory.ref(meta.ext.inv.getRef())).app(normConsistSubExpr).build()).build();
      if (concatNFsProof == null) {
      //  return new SubexprOccurrences(null, null, null, allOccurrences.size());
        result.equalityProof = factory.appBuilder(factory.ref(meta.ext.concat.getRef())).app(normConsistExpr)
                .app(pmapOccurrence).build();
      } else {
        result.equalityProof = factory.appBuilder(factory.ref(meta.ext.concat.getRef())).app(normConsistExpr)
                .app(factory.appBuilder(factory.ref(meta.ext.concat.getRef())).app(concatNFsProof).app(pmapOccurrence).build()).build();
      }
      result.wrapExprWithOccurrences(factory.core(subExpr.getType().computeTyped()), factory);
      return result;
    }

    return null;
  }

  @Override
  public ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter) {
    CompiledTerm term1 = lastTerm == leftExpr ? lastCompiled : compileTerm(leftExpr.getExpression());
    CompiledTerm term2 = compileTerm(rightExpr.getExpression());
    lastTerm = rightExpr;
    lastCompiled = term2;

    // TODO: get rid of this shit with flags
    boolean oldCommutative = isCommutative;
    boolean commutative = false;
    if (isCommutative && !term1.nf.equals(term2.nf)) {
      commutative = true;
      term1.nf = CountingSort.sort(term1.nf);
      term2.nf = CountingSort.sort(term2.nf);
    }
    isCommutative = commutative;

    boolean oldSemilattice = isSemilattice;
    boolean semilattice = false;
    if (isSemilattice && commutative && !term1.nf.equals(term2.nf)) {
      semilattice = true;
      term1.nf = removeDuplicates(term1.nf);
      term2.nf = removeDuplicates(term2.nf);
    }
    isSemilattice = semilattice;

    ConcreteExpression lastArgument;
    if (!term1.nf.equals(term2.nf)) {
      if (!useHypotheses) {
        errorReporter.report(new MonoidSolverError(isMultiplicative, term1.nf, term2.nf, values.getValues(), Collections.emptyList(), Collections.emptyList(),  Collections.emptyList(), hint != null ? hint : refExpr));
        return null;
      }

      List<RuleExt> rules = new ArrayList<>();
      if (contextRules == null) {
        contextRules = new HashMap<>();
      }
      ContextHelper helper = new ContextHelper(hint);
      for (CoreBinding binding : helper.getContextBindings(typechecker)) {
        rules.addAll(contextRules.computeIfAbsent(binding, k -> {
          List<RuleExt> ctxList = new ArrayList<>();
          typeToRule(null, binding, false, ctxList);
          return ctxList;
        }));
      }
      for (CoreBinding binding : helper.getAdditionalBindings(typechecker)) {
        typeToRule(null, binding, true, rules);
      }

      if (isCommutative) {
        ComMonoidWPSolver solver = new ComMonoidWPSolver();
        var equalities = new ArrayList<Equality>();
        for (RuleExt rule : rules) {
          if (rule.direction == Direction.FORWARD || rule.direction == Direction.UNKNOWN) {
            equalities.add(new Equality(rule.binding != null ? factory.ref(rule.binding) : factory.core(rule.expression), rule.lhsTerm, rule.rhsTerm, rule.lhs, rule.rhs));
          } else {
            equalities.add(new Equality(rule.binding != null ? factory.ref(rule.binding) : factory.core(rule.expression), rule.rhsTerm, rule.lhsTerm, rule.rhs, rule.lhs));
          }
        }
        isCommutative = oldCommutative;
        isSemilattice = oldSemilattice;
        ConcreteExpression result = solver.solve(term1, term2, equalities);
        if (result == null) {
          errorReporter.report(new MonoidSolverError(isMultiplicative, term1.nf, term2.nf, values.getValues(), rules, Collections.emptyList(), Collections.emptyList(), hint != null ? hint : refExpr));
        }
        return result;
      }

      List<Step> trace1 = new ArrayList<>();
      List<Step> trace2 = new ArrayList<>();
      List<Integer> newNf1 = applyRules(term1.nf, rules, trace1);
      List<Integer> newNf2 = applyRules(term2.nf, rules, trace2);
      if (!newNf1.equals(newNf2)) {
        isCommutative = oldCommutative;
        isSemilattice = oldSemilattice;
        errorReporter.report(new MonoidSolverError(isMultiplicative, term1.nf, term2.nf, values.getValues(), rules, trace1, trace2, hint != null ? hint : refExpr));
        return null;
      }

      while (!trace1.isEmpty() && !trace2.isEmpty()) {
        if (trace1.get(trace1.size() - 1).equals(trace2.get(trace2.size() - 1))) {
          trace1.remove(trace1.size() - 1);
          trace2.remove(trace2.size() - 1);
        } else {
          break;
        }
      }

      for (Step step : trace1) {
        step.rule.count++;
      }
      for (Step step : trace2) {
        step.rule.count++;
      }
      for (RuleExt rule : rules) {
        if (rule.count > 0) {
          if (rule.rnfTerm == null) {
            rule.rnfTerm = computeNFTerm(rule.rhs);
          }
          if (rule.cExpr != null) {
            continue;
          }

          ConcreteExpression cExpr = rule.binding != null ? factory.ref(rule.binding) : factory.core(null, rule.expression);
          if (rule.direction == Direction.BACKWARD) {
            cExpr = factory.app(factory.ref(meta.ext.inv.getRef()), true, singletonList(cExpr));
          }
          if (!isNF(rule.lhsTerm) || !isNF(rule.rhsTerm)) {
            cExpr = factory.appBuilder(factory.ref(meta.termsEqConv.getRef()))
              .app(factory.ref(dataRef), false)
              .app(rule.lhsTerm)
              .app(rule.rhsTerm)
              .app(cExpr)
              .build();
          }
          if (rule.count > 1 && !(cExpr instanceof ConcreteReferenceExpression) || rule.binding == null) {
            ArendRef letClause = factory.local("rule" + letClauses.size());
            letClauses.add(factory.letClause(letClause, Collections.emptyList(), null, cExpr));
            rule.cExpr = factory.ref(letClause);
          } else {
            rule.cExpr = cExpr;
          }
        }
      }

      ConcreteExpression expr1 = trace1.isEmpty() ? null : traceToExpr(term1.nf, trace1, dataRef, factory);
      ConcreteExpression expr2 = trace2.isEmpty() ? null : factory.app(factory.ref(meta.ext.inv.getRef()), true, singletonList(traceToExpr(term2.nf, trace2, dataRef, factory)));
      if (expr1 == null && expr2 == null) {
        lastArgument = factory.ref(meta.ext.prelude.getIdpRef());
      } else if (expr2 == null) {
        lastArgument = expr1;
      } else if (expr1 == null) {
        lastArgument = expr2;
      } else {
        lastArgument = factory.appBuilder(factory.ref(meta.ext.concat.getRef())).app(expr1).app(expr2).build();
      }
    } else {
      lastArgument = factory.ref(meta.ext.prelude.getIdpRef());
    }

    ConcreteAppBuilder builder = factory.appBuilder(factory.ref((isCat ? meta.catTermsEq : semilattice ? meta.semilatticeTermsEq : commutative ? meta.commTermsEq : meta.termsEq).getRef()))
      .app(factory.ref(dataRef), false);
    if (isCat) {
      CoreExpression type = leftExpr.getType().normalize(NormalizationMode.WHNF);
      if (type instanceof CoreAppExpression) {
        CoreExpression fun = ((CoreAppExpression) type).getFunction().normalize(NormalizationMode.WHNF);
        if (fun instanceof CoreAppExpression) {
          int dom = obValues.addValue(((CoreAppExpression) fun).getArgument());
          int cod = obValues.addValue(((CoreAppExpression) type).getArgument());
          builder.app(factory.number(dom), false).app(factory.number(cod), false);
        }
      }
    }
    isCommutative = oldCommutative;
    isSemilattice = oldSemilattice;
    return builder
      .app(term1.concrete)
      .app(term2.concrete)
      .app(lastArgument)
      .build();
  }

  private static class Equality {
    public final ConcreteExpression binding;
    public List<Integer> lhsNF;
    public List<Integer> rhsNF;
    public ConcreteExpression lhsTerm;
    public ConcreteExpression rhsTerm;

    private Equality(ConcreteExpression binding, ConcreteExpression lhsTerm, ConcreteExpression rhsTerm, List<Integer> lhsNF, List<Integer> rhsNF) {
      this.binding = binding;
      this.lhsTerm = lhsTerm;
      this.rhsTerm = rhsTerm;
      this.lhsNF = lhsNF;
      this.rhsNF = rhsNF;
    }
  }

  private class ComMonoidWPSolver {

    public ConcreteExpression solve(CompiledTerm term1, CompiledTerm term2, List<Equality> axioms) {
      int alphabetSize = term1.nf.isEmpty() ? 0 : Collections.max(term1.nf) + 1;
      alphabetSize = term2.nf.isEmpty() ? alphabetSize : Integer.max(alphabetSize, Collections.max(term2.nf) + 1);
      for (Equality axiom : axioms) {
        if (!axiom.lhsNF.isEmpty()) {
          alphabetSize = Integer.max(alphabetSize, Collections.max(axiom.lhsNF) + 1);
        }
        if (!axiom.rhsNF.isEmpty()) {
          alphabetSize = Integer.max(alphabetSize, Collections.max(axiom.rhsNF) + 1);
        }
      }

      var word1Pow = ComMonoidWP.elemsSeqToPowersSeq(term1.nf, alphabetSize);
      var word2Pow = ComMonoidWP.elemsSeqToPowersSeq(term2.nf, alphabetSize);
      List<Pair<List<Integer>, List<Integer>>> axiomsPow = new ArrayList<>();

      for (Equality axiom : axioms) {
        axiomsPow.add(new Pair<>(ComMonoidWP.elemsSeqToPowersSeq(axiom.lhsNF, alphabetSize), ComMonoidWP.elemsSeqToPowersSeq(axiom.rhsNF, alphabetSize)));
      }

      var wpAlgorithm = new ComMonoidWP(new GroebnerIM(new Buchberger()));
      var axiomsToApply = wpAlgorithm.solve(word1Pow, word2Pow, axiomsPow);

      List<Integer> curWord = new ArrayList<>(term1.nf);

      if (axiomsToApply == null) return null;

      ConcreteExpression proofTerm = null;

      for (Pair<Integer, Boolean> axiom : axiomsToApply) {
        var equalityToApply = axioms.get(axiom.proj1);
        var isDirect = axiom.proj2;
        var powsToRemove = isDirect ? axiomsPow.get(axiom.proj1).proj1 : axiomsPow.get(axiom.proj1).proj2;
        var rhsNF = isDirect ? equalityToApply.rhsNF : equalityToApply.lhsNF;
        var lhsTerm = isDirect ? equalityToApply.lhsTerm : equalityToApply.rhsTerm;
        var rhsTerm = isDirect ? equalityToApply.rhsTerm : equalityToApply.lhsTerm;
        ConcreteExpression rhsTermNF = computeNFTerm(rhsNF);
        ConcreteExpression nfProofTerm = equalityToApply.binding; // factory.ref(equalityToApply.binding);

        if (!isDirect) {
          nfProofTerm = factory.app(factory.ref(meta.ext.inv.getRef()), true, singletonList(nfProofTerm));
        }

        //if (!isNF(equalityToApply.lhsTerm) || !isNF(equalityToApply.rhsTerm)) {
          nfProofTerm = factory.appBuilder(factory.ref(meta.commTermsEqConv.getRef()))
                  .app(factory.ref(dataRef), false)
                  .app(lhsTerm)
                  .app(rhsTerm)
                  .app(nfProofTerm)
                  .build();
        //}

        var indexesToReplace = ComMonoidWP.findIndexesToRemove(curWord, powsToRemove);
        var subwordToReplace = new ArrayList<Integer>();
        var newWord = new ArrayList<>(curWord);

        for (Integer integer : indexesToReplace) {
          subwordToReplace.add(newWord.get(integer));
          newWord.remove(integer.intValue());
        }

        int prefix = 0;
        for (int i = 0; i < indexesToReplace.size(); ++i) {
          int ind = indexesToReplace.get(i);
          indexesToReplace.set(i, ind + i - prefix);
          prefix = ind + i + 1;
        }

        for (int i = rhsNF.size() - 1; i >= 0; --i) {
          newWord.add(0, rhsNF.get(i));
        }

        if (subwordToReplace.size() > 1) {
          ConcreteExpression sortProofLeft = factory.appBuilder(factory.ref(meta.sortDef.getRef())).app(computeNFTerm(subwordToReplace)).build();
          nfProofTerm = factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(sortProofLeft, nfProofTerm));
        }
        ConcreteExpression sortProofRight = factory.appBuilder(factory.ref(meta.sortDef.getRef())).app(rhsTermNF).build();
        sortProofRight = factory.app(factory.ref(meta.ext.inv.getRef()), true, singletonList(sortProofRight));
        nfProofTerm = factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(nfProofTerm, sortProofRight));

        ConcreteExpression stepProofTerm = factory.appBuilder(factory.ref(meta.commReplaceDef.getRef()))
                .app(factory.ref(dataRef), false)
                .app(computeNFTerm(curWord))
                .app(computeNFTerm(indexesToReplace))
                .app(rhsTermNF)
                .app(nfProofTerm)
                .build();
        if (proofTerm == null) {
          proofTerm = stepProofTerm;
        } else {
          proofTerm = factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(proofTerm, stepProofTerm));
        }

        curWord = newWord;
      }

      if (proofTerm == null) {
        proofTerm = factory.ref(meta.ext.prelude.getIdpRef());
      } else {
        ConcreteExpression sortProof = factory.appBuilder(factory.ref(meta.sortDef.getRef())).app(computeNFTerm(curWord)).build();
        proofTerm = factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(proofTerm, sortProof));
      }

      return factory.appBuilder(factory.ref(meta.commTermsEq.getRef()))
              .app(factory.ref(dataRef), false)
              .app(term1.concrete)
              .app(term2.concrete)
              .app(proofTerm)
              .build();
    }
  }


  private boolean typeToRule(TypedExpression typed, CoreBinding binding, boolean alwaysForward, List<RuleExt> rules) {
    if (binding == null && typed == null) {
      return false;
    }
    CoreExpression type = binding != null ? binding.getTypeExpr() : typed.getType();
    CoreFunCallExpression eq = Utils.toEquality(type, null, null);
    if (eq == null) {
      CoreExpression typeNorm = type.normalize(NormalizationMode.WHNF);
      if (!(typeNorm instanceof CoreClassCallExpression classCall)) {
        return false;
      }
      boolean isLDiv = classCall.getDefinition().isSubClassOf(meta.ldiv);
      boolean isRDiv = classCall.getDefinition().isSubClassOf(meta.rdiv);
      if (!isLDiv && !isRDiv) {
        return false;
      }
      List<ConcreteExpression> args = singletonList(binding != null ? factory.ref(binding) : factory.core(null, typed));
      return (!isLDiv || typeToRule(typechecker.typecheck(factory.app(factory.ref(meta.ldiv.getPersonalFields().get(0).getRef()), false, args), null), null, true, rules)) &&
        (!isRDiv || typeToRule(typechecker.typecheck(factory.app(factory.ref(meta.rdiv.getPersonalFields().get(0).getRef()), false, args), null), null, true, rules));
    }

    if (!typechecker.compare(eq.getDefCallArguments().get(0), getValuesType(), CMP.EQ, refExpr, false, true, false)) {
      return false;
    }

    List<Integer> lhs = new ArrayList<>();
    List<Integer> rhs = new ArrayList<>();
    ConcreteExpression lhsTerm = computeTerm(eq.getDefCallArguments().get(1), lhs);
    ConcreteExpression rhsTerm = computeTerm(eq.getDefCallArguments().get(2), rhs);
    if (binding == null) {
      rules.add(new RuleExt(typed, null, Direction.FORWARD, lhs, rhs, lhsTerm, rhsTerm));
    } else {
      Direction direction = alwaysForward || lhs.size() > rhs.size() ? Direction.FORWARD : Direction.UNKNOWN;
      RuleExt rule = new RuleExt(typed, binding, direction, lhs, rhs, lhsTerm, rhsTerm);
      if (!alwaysForward && lhs.size() < rhs.size()) {
        rule.setBackward();
      }
      rules.add(rule);
    }
    return true;
  }

  private static final int MAX_STEPS = 100;

  private List<Integer> applyRules(List<Integer> term, List<RuleExt> rules, List<Step> trace) {
    boolean hasBadRules = false;
    for (RuleExt rule : rules) {
      if (rule.isIncreasing()) {
        hasBadRules = true;
        break;
      }
    }

    int i = 0;
    boolean found;
    do {
      found = false;
      for (RuleExt rule : rules) {
        int pos = Collections.indexOfSubList(term, rule.lhs);
        if (rule.direction == Direction.UNKNOWN) {
          if (pos < 0) {
            pos = Collections.indexOfSubList(term, rule.rhs);
            if (pos >= 0) {
              rule.setBackward();
            }
          } else {
            rule.direction = Direction.FORWARD;
          }
          if (rule.isIncreasing()) {
            hasBadRules = true;
          }
        }
        if (pos >= 0) {
          Step step = new Step(rule, pos);
          trace.add(step);
          term = step.apply(term);
          found = true;
          break;
        }
      }
      i++;
    } while (found && (!hasBadRules || i < MAX_STEPS));

    return term;
  }

  private ConcreteExpression traceToExpr(List<Integer> nf, List<Step> trace, ArendRef dataRef, ConcreteFactory factory) {
    ConcreteExpression result = null;
    for (Step step : trace) {
      ConcreteExpression expr = factory.appBuilder(factory.ref(meta.replaceDef.getRef()))
        .app(factory.ref(dataRef), false)
        .app(computeNFTerm(nf))
        .app(factory.number(step.position))
        .app(factory.number(step.rule.lhs.size()))
        .app(step.rule.rnfTerm)
        .app(step.rule.cExpr)
        .build();
      if (result == null) {
        result = expr;
      } else {
        result = factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(result, expr));
      }
      nf = step.apply(nf);
    }
    return result;
  }

  private static boolean isNF(ConcreteExpression term) {
    return term instanceof ConcreteReferenceExpression || isNFRec(term);
  }

  private static boolean isNFRec(ConcreteExpression term) {
    if (!(term instanceof ConcreteAppExpression)) {
      return false;
    }
    List<? extends ConcreteArgument> args = ((ConcreteAppExpression) term).getArguments();
    return args.size() == 1 || args.size() == 2 && args.get(0).getExpression() instanceof ConcreteAppExpression && ((ConcreteAppExpression) args.get(0).getExpression()).getArguments().size() == 1 && isNF(args.get(1).getExpression());
  }

  private ConcreteExpression computeNFTerm(List<Integer> nf) {
    if (isCat) {
      ConcreteExpression result = factory.appBuilder(factory.ref(meta.nilCatNF.getRef())).app(factory.ref(meta.ext.prelude.getIdpRef())).build();
      ConcreteExpression hdata = factory.appBuilder(factory.ref(meta.HDataFunc.getRef())).app(factory.ref(dataRef), false).build();
      ConcreteExpression vdata = factory.appBuilder(factory.ref(meta.VDataFunc.getRef())).app(factory.ref(dataRef), false).build();
      Integer domNF = null;
      for (int i = nf.size() - 1; i >= 0; i--) {
        int dom = domMap.get(nf.get(i));
        int codom = codomMap.get(nf.get(i));
        int localIndex = homMap.get(new Pair<>(dom, codom)).get(nf.get(i));
        if (domNF == null) {
          domNF = dom;
        }
        result = factory.appBuilder(factory.ref(meta.consCatNF.getRef()))
                //.app(factory.ref(meta.ext.prelude.getNat().getRef()), false)
                .app(vdata, false)
                .app(factory.number(domNF), false)
                .app(factory.number(codom), false)
                .app(hdata, false)
                .app(factory.number(dom), false)
                .app(factory.number(localIndex))
                .app(result).build();
      }
      return result;
    }
    return formList(nf.stream().map(factory::number).collect(Collectors.toList()), factory, meta.ext.nil, meta.ext.cons);
  }

  // TODO: create a proper util method somewhere else instead of this
  public static ConcreteExpression formList(List<ConcreteExpression> nf, ConcreteFactory factory, CoreConstructor nil, CoreConstructor cons) {
    ConcreteExpression result = factory.ref(nil.getRef());
    for (int i = nf.size() - 1; i >= 0; i--) {
      result = factory.appBuilder(factory.ref(cons.getRef())).app(nf.get(i)).app(result).build();
    }
    return result;
  }

  public enum Direction { FORWARD, BACKWARD, UNKNOWN }

  public static class Step {
    private final RuleExt rule;
    private final int position;

    private Step(RuleExt rule, int position) {
      this.rule = rule;
      this.position = position;
    }

    public List<Integer> apply(List<Integer> term) {
      if (term.size() < position + rule.lhs.size()) {
        return null;
      }
      List<Integer> result = new ArrayList<>(term.size() - rule.lhs.size() + rule.rhs.size());
      for (int i = 0; i < position; i++) {
        result.add(term.get(i));
      }
      result.addAll(rule.rhs);
      for (int i = position + rule.lhs.size(); i < term.size(); i++) {
        result.add(term.get(i));
      }
      return result;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      Step step = (Step) o;
      return position == step.position && rule.equals(step.rule);
    }

    @Override
    public int hashCode() {
      return Objects.hash(rule, position);
    }
  }

  public static class Rule {
    public final TypedExpression expression;
    public final CoreBinding binding;
    public Direction direction;
    public List<Integer> lhs;
    public List<Integer> rhs;

    private Rule(TypedExpression expression, CoreBinding binding, Direction direction, List<Integer> lhs, List<Integer> rhs) {
      this.expression = expression;
      this.binding = binding;
      this.direction = direction;
      this.lhs = lhs;
      this.rhs = rhs;
    }

    boolean isIncreasing() {
      return direction == Direction.UNKNOWN ? lhs.size() == rhs.size() : lhs.size() <= rhs.size();
    }
  }

  private static class RuleExt extends Rule {
    private ConcreteExpression lhsTerm;
    private ConcreteExpression rhsTerm;
    private int count;
    private ConcreteExpression cExpr;
    private ConcreteExpression rnfTerm;

    private RuleExt(TypedExpression expression, CoreBinding binding, Direction direction, List<Integer> lhs, List<Integer> rhs, ConcreteExpression lhsTerm, ConcreteExpression rhsTerm) {
      super(expression, binding, direction, lhs, rhs);
      this.lhsTerm = lhsTerm;
      this.rhsTerm = rhsTerm;
    }

    private void setBackward() {
      if (direction == Direction.BACKWARD) {
        return;
      }
      direction = Direction.BACKWARD;
      List<Integer> nf = rhs;
      rhs = lhs;
      lhs = nf;
      ConcreteExpression term = rhsTerm;
      rhsTerm = lhsTerm;
      lhsTerm = term;
    }
  }

  private static class CompiledTerm {
    private final ConcreteExpression concrete;
    private List<Integer> nf;

    private CompiledTerm(ConcreteExpression concrete, List<Integer> nf) {
      this.concrete = concrete;
      this.nf = nf;
    }
  }

  private CompiledTerm compileTerm(CoreExpression expression) {
    List<Integer> nf = new ArrayList<>();
    return new CompiledTerm(computeTerm(expression, nf), nf);
  }

  private ConcreteExpression computeTerm(CoreExpression expression, List<Integer> nf) {
    CoreExpression expr = expression.normalize(NormalizationMode.WHNF);
    int dom = -1, cod = -1;
    ConcreteExpression hdata = isCat ? factory.appBuilder(factory.ref(meta.HDataFunc.getRef())).app(factory.ref(dataRef), false).build() : null;
    ConcreteExpression vdata = isCat ? factory.appBuilder(factory.ref(meta.VDataFunc.getRef())).app(factory.ref(dataRef), false).build() : null;

    if (isCat) {
      CoreExpression type = expr.computeType().normalize(NormalizationMode.WHNF);
      if (type instanceof CoreAppExpression) {
        CoreExpression fun = ((CoreAppExpression) type).getFunction().normalize(NormalizationMode.WHNF);
        if (fun instanceof CoreAppExpression) {
          dom = obValues.addValue(((CoreAppExpression) fun).getArgument());
          cod = obValues.addValue(((CoreAppExpression) type).getArgument());
        }
      }
    }

    if (ideMatcher.match(expr) != null) {
      if (isCat) {
        if (dom != -1 && cod != -1) {
          return factory.appBuilder(factory.ref(meta.idCTerm.getRef()))
                  .app(vdata, false)
                  .app(factory.number(dom), false)
                  .app(factory.number(cod), false)
                  .app(hdata, false)
                  .app(factory.ref(meta.ext.prelude.getIdpRef()))
                  .build();
        }
      }
      return isCat ? factory.app(factory.ref(meta.idCTerm.getRef()), true, singletonList(factory.ref(meta.ext.prelude.getIdpRef()))) : factory.ref(meta.ideMTerm.getRef());
    }


    List<CoreExpression> args = mulMatcher.match(expr);
    if (args != null) {
      List<ConcreteExpression> cArgs = new ArrayList<>();
      List<ConcreteExpression> implArgs = new ArrayList<>();
      var left = computeTerm(args.get(args.size() - 2), nf);
      var right = computeTerm(args.get(args.size() - 1), nf);
      if (isCat) {
        if (dom != -1 && cod != -1) {
          implArgs.add(vdata);
          implArgs.add(factory.number(dom));
          implArgs.add(factory.number(cod));
          implArgs.add(hdata);
        }
        cArgs.add(factory.number(obValues.addValue(args.get(1))));
      }
      cArgs.add(left);
      cArgs.add(right);
      ConcreteExpression comp = factory.ref((isCat ? meta.compCTerm : meta.mulMTerm).getRef());
      if (!implArgs.isEmpty()) {
        comp = factory.app(comp, false, implArgs);
      }
      return factory.app(comp, true, cArgs);
    }

    int index = values.addValue(expr);
    nf.add(index);
    if (isCat) {
      if (dom != -1 && cod != -1) {
        domMap.put(index, dom);
        codomMap.put(index, cod);
        Map<Integer, Integer> list = homMap.computeIfAbsent(new Pair<>(dom, cod), k -> new HashMap<>());
        int newIndex = list.size();
        Integer prev = list.putIfAbsent(index, newIndex);
        index = prev != null ? prev : newIndex;
      }
    }
    return factory.app(factory.ref((isCat ? meta.varCTerm : meta.varMTerm).getRef()), true, singletonList(factory.number(index)));
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    DataFactory dataFactory;

    if (!isCat) {
      dataFactory = new MonoidDataFactory(meta, dataRef, values, letClauses, factory, instance, isSemilattice, isCommutative, isMultiplicative);
    } else {
      dataFactory = new CategoryDataFactory(meta, dataRef, values, obValues, homMap, factory, instance);
    }

    return typechecker.typecheck(dataFactory.wrapWithData(result), null);
  }
}
