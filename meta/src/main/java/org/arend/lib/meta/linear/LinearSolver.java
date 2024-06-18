package org.arend.lib.meta.linear;

import org.arend.ext.concrete.ConcreteAppBuilder;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.InstanceInferenceError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.error.LinearSolverError;
import org.arend.lib.error.TypeError;
import org.arend.lib.meta.solver.BaseTermCompiler;
import org.arend.lib.meta.solver.RingKind;
import org.arend.lib.util.DefImplInstanceSearchParameters;
import org.arend.lib.util.RelationData;
import org.arend.lib.util.Utils;

import java.math.BigInteger;
import java.util.*;

public class LinearSolver {
  private final Map<CoreDefinition, Pair<TypedExpression, CoreClassField>> instanceCache = new HashMap<>();
  private final ExpressionTypechecker typechecker;
  private final ErrorReporter errorReporter;
  private final ConcreteSourceNode marker;
  private final StdExtension ext;
  private final ConcreteFactory factory;

  public LinearSolver(ExpressionTypechecker typechecker, ConcreteSourceNode marker, StdExtension ext) {
    this.typechecker = typechecker;
    errorReporter = typechecker.getErrorReporter();
    this.marker = marker;
    this.ext = ext;
    factory = ext.factory.withData(marker);
  }

  private CoreClassDefinition getInstanceClass() {
    return ext.equationMeta.LinearlyOrderedSemiring;
  }

  private CoreExpression findInstance(CoreExpression type, boolean reportError) {
    TypedExpression instance = type == null ? null : typechecker.findInstance(getInstanceClass(), type, null, marker);
    if (instance == null) {
      if (reportError) errorReporter.report(new InstanceInferenceError(typechecker.getExpressionPrettifier(), getInstanceClass().getRef(), type, marker));
      return null;
    }
    return instance.getExpression();
  }

  private void reportTypeError(CoreExpression expectedType) {
    typechecker.getErrorReporter().report(new TypeError(typechecker.getExpressionPrettifier(), "The expected type should be either an equation or the empty type", expectedType, marker));
  }

  private Hypothesis<CoreExpression> typeToEquation(CoreExpression type, CoreBinding binding, boolean reportError) {
    ConcreteExpression expr = binding == null ? null : factory.ref(binding);
    if (expr != null && type instanceof CorePiExpression) {
      ConcreteExpression newExpr = expr;
      while (type instanceof CorePiExpression) {
        List<ConcreteArgument> args = new ArrayList<>();
        for (CoreParameter param = ((CorePiExpression) type).getParameters(); param.hasNext(); param = param.getNext()) {
          args.add(factory.arg(factory.hole(), param.isExplicit()));
        }
        newExpr = factory.app(newExpr, args);
        type = ((CorePiExpression) type).getCodomain().normalize(NormalizationMode.WHNF);
      }
      TypedExpression typedExpr = typechecker.typecheck(newExpr, null);
      if (typedExpr != null) {
        expr = factory.core(typedExpr);
        type = typedExpr.getType();
      }
    }

    CoreFunCallExpression eq = type.toEquality();
    if (eq != null) {
      CoreExpression instance = findInstance(eq.getDefCallArguments().get(0), reportError);
      if (instance == null) return null;
      return new Hypothesis<>(expr, instance, Equation.Operation.EQUALS, eq.getDefCallArguments().get(1), eq.getDefCallArguments().get(2), BigInteger.ONE);
    }

    RelationData relationData = RelationData.getRelationData(type.normalize(NormalizationMode.WHNF));
    if (relationData == null) {
      if (reportError) reportTypeError(type);
      return null;
    }
    if (relationData.defCall instanceof CoreFieldCallExpression fieldCall) {
      CoreClassField field = fieldCall.getDefinition();
      if (field == ext.equationMeta.less || field == ext.equationMeta.lessOrEquals) {
        CoreExpression arg = fieldCall.getArgument();
        CoreExpression argType = arg.computeType().normalize(NormalizationMode.WHNF);
        if (argType instanceof CoreClassCallExpression classCall && classCall.getDefinition().isSubClassOf(getInstanceClass())) {
          return new Hypothesis<>(expr, arg, field == ext.equationMeta.less ? Equation.Operation.LESS : Equation.Operation.LESS_OR_EQUALS, relationData.leftExpr, relationData.rightExpr, BigInteger.ONE);
        } else {
          if (reportError) errorReporter.report(new TypeError(typechecker.getExpressionPrettifier(), "", argType, marker) {
            @Override
            public LineDoc getShortHeaderDoc(PrettyPrinterConfig ppConfig) {
              return DocFactory.hList(DocFactory.text("The type of the equation should be "), DocFactory.refDoc(getInstanceClass().getRef()));
            }
          });
          return null;
        }
      }
      if (reportError) reportTypeError(type);
      return null;
    }

    if (relationData.defCall.getDefinition() == ext.equationMeta.linearOrederLeq) {
      return new Hypothesis<>(expr, relationData.defCall.getDefCallArguments().get(0), Equation.Operation.LESS_OR_EQUALS, relationData.leftExpr, relationData.rightExpr, BigInteger.ONE);
    }

    if (relationData.defCall.getDefinition() == ext.equationMeta.addGroupLess) {
      CoreExpression instance = relationData.defCall.getDefCallArguments().get(0);
      TypedExpression typedInstance = instance.computeTyped();
      CoreExpression instanceType = typedInstance.getType().normalize(NormalizationMode.WHNF);
      if (!(instanceType instanceof CoreClassCallExpression classCall && classCall.getDefinition().isSubClassOf(getInstanceClass()))) {
        instance = findInstance(instanceType instanceof CoreClassCallExpression classCall ? Utils.getClassifyingExpression(classCall, typedInstance) : null, reportError);
        if (instance == null) return null;
      }
      return new Hypothesis<>(expr, instance, Equation.Operation.LESS, relationData.leftExpr, relationData.rightExpr, BigInteger.ONE);
    }

    var pair = instanceCache.computeIfAbsent(relationData.defCall.getDefinition(), def -> {
      DefImplInstanceSearchParameters parameters = new DefImplInstanceSearchParameters(def) {
        @Override
        protected List<CoreClassField> getRelationFields(CoreClassDefinition classDef) {
          return classDef.isSubClassOf(getInstanceClass()) ? Arrays.asList(ext.equationMeta.less, ext.equationMeta.lessOrEquals) : Collections.emptyList();
        }
      };
      TypedExpression instance = typechecker.findInstance(parameters, null, null, marker);
      return instance == null ? null : new Pair<>(instance, parameters.getRelationField());
    });
    if (pair == null) {
      if (reportError) reportTypeError(type);
      return null;
    }
    return new Hypothesis<>(expr, pair.proj1.getExpression(), pair.proj2 == ext.equationMeta.less ? Equation.Operation.LESS : Equation.Operation.LESS_OR_EQUALS, relationData.leftExpr, relationData.rightExpr, BigInteger.ONE);
  }

  private static class Hypothesis<E> extends Equation<E> {
    public final ConcreteExpression proof;
    private final BigInteger lcm;

    private Hypothesis(ConcreteExpression proof, CoreExpression instance, Operation operation, E lhsTerm, E rhsTerm, BigInteger lcm) {
      super(instance, operation, lhsTerm, rhsTerm);
      this.proof = proof;
      this.lcm = lcm;
    }

    @Override
    public BigInteger getLCM() {
      return lcm;
    }
  }

  private Hypothesis<CoreExpression> bindingToHypothesis(CoreBinding binding) {
    return binding == null ? null : typeToEquation(binding.getTypeExpr().normalize(NormalizationMode.WHNF), binding, false);
  }

  private List<BigInteger> solveEquations(List<? extends Equation<CompiledTerm>> equations, int var) {
    if (equations.isEmpty()) {
      return null;
    }

    if (var < 0) {
      List<BigInteger> result = new ArrayList<>(equations.size());
      boolean found = false;
      for (Equation<CompiledTerm> equation : equations) {
        if (!found && equation.operation == Equation.Operation.LESS) {
          result.add(BigInteger.ONE);
          found = true;
        } else {
          result.add(BigInteger.ZERO);
        }
      }
      return found ? result : null;
    }

    Map<Integer, Integer> indexMap1 = new HashMap<>(); // maps an index in equations to an index in newEquations
    Map<Integer, List<Pair<Integer, BigInteger>>> indexMap2 = new HashMap<>(); // maps an index in equations to a set of pairs of the form (an index in newEquations, a coefficient)
    List<Equation<CompiledTerm>> newEquations = new ArrayList<>();
    for (int j1 = 0; j1 < equations.size(); j1++) {
      Equation<CompiledTerm> equation1 = equations.get(j1);
      int cmp1 = equation1.lhsTerm.getCoef(var).compareTo(equation1.rhsTerm.getCoef(var));
      if (cmp1 == 0) {
        indexMap1.put(j1, newEquations.size());
        newEquations.add(equation1);
        continue;
      }

      for (int j2 = 0; j2 < j1; j2++) {
        equation1 = equations.get(j1);
        Equation<CompiledTerm> equation2 = equations.get(j2);
        int cmp2 = equation2.lhsTerm.getCoef(var).compareTo(equation2.rhsTerm.getCoef(var));
        if (cmp2 == 0) continue;

        if (!(cmp1 < 0 && cmp2 > 0 || cmp1 > 0 && cmp2 < 0)) {
          continue;
        }
        boolean swap = cmp1 > 0;
        if (swap) {
          Equation<CompiledTerm> tmp = equation1;
          equation1 = equation2;
          equation2 = tmp;
        }

        BigInteger c1 = equation1.rhsTerm.getCoef(var).subtract(equation1.lhsTerm.getCoef(var));
        BigInteger c2 = equation2.lhsTerm.getCoef(var).subtract(equation2.rhsTerm.getCoef(var));
        BigInteger gcd = c1.gcd(c2);
        BigInteger d1 = c2.divide(gcd);
        BigInteger d2 = c1.divide(gcd);
        List<BigInteger> lhs = new ArrayList<>();
        List<BigInteger> rhs = new ArrayList<>();
        for (int i = 0; i < var; i++) {
          lhs.add(d1.multiply(equation1.lhsTerm.getCoef(i)).add(d2.multiply(equation2.lhsTerm.getCoef(i))));
          rhs.add(d1.multiply(equation1.rhsTerm.getCoef(i)).add(d2.multiply(equation2.rhsTerm.getCoef(i))));
        }

        indexMap2.computeIfAbsent(j1, k -> new ArrayList<>()).add(new Pair<>(newEquations.size(), swap ? d2 : d1));
        indexMap2.computeIfAbsent(j2, k -> new ArrayList<>()).add(new Pair<>(newEquations.size(), swap ? d1 : d2));

        newEquations.add(new Equation<>(null, equation1.operation == Equation.Operation.EQUALS && equation2.operation == Equation.Operation.EQUALS
          ? Equation.Operation.EQUALS
          : equation1.operation == Equation.Operation.LESS || equation2.operation == Equation.Operation.LESS
            ? Equation.Operation.LESS
            : Equation.Operation.LESS_OR_EQUALS,
          new CompiledTerm(null, lhs, Collections.emptySet()), new CompiledTerm(null, rhs, Collections.emptySet())));
      }
    }

    List<BigInteger> solution = solveEquations(newEquations, var - 1);
    if (solution == null) return null;
    List<BigInteger> result = new ArrayList<>(equations.size());
    for (int i = 0; i < equations.size(); i++) {
      Integer j = indexMap1.get(i);
      if (j != null) {
        result.add(solution.get(j));
      } else {
        List<Pair<Integer, BigInteger>> list = indexMap2.get(i);
        if (list != null) {
          BigInteger s = BigInteger.ZERO;
          for (Pair<Integer, BigInteger> pair : list) {
            s = s.add(solution.get(pair.proj1).multiply(pair.proj2));
          }
          result.add(s);
        } else {
          result.add(BigInteger.ZERO);
        }
      }
    }
    return result;
  }

  private TermCompiler makeTermCompiler(TypedExpression instance, CoreClassCallExpression classCall) {
    return classCall == null ? null : new TermCompiler(classCall, instance, ext, typechecker, marker);
  }

  private void compileHypotheses(TermCompiler compiler, List<Hypothesis<CoreExpression>> equations, List<Hypothesis<CompiledTerm>> result) {
    for (Hypothesis<CoreExpression> hypothesis : equations) {
      CompiledTerms terms = compiler.compileTerms(hypothesis.lhsTerm, hypothesis.rhsTerm);
      if (hypothesis.operation == Equation.Operation.EQUALS) {
        result.add(new Hypothesis<>(factory.app(factory.ref(ext.linearSolverMeta.eqToLeq.getRef()), true, hypothesis.proof), hypothesis.instance, Equation.Operation.LESS_OR_EQUALS, terms.term1, terms.term2, terms.lcm));
        result.add(new Hypothesis<>(factory.app(factory.ref(ext.linearSolverMeta.eqToLeq.getRef()), true, factory.app(factory.ref(ext.inv.getRef()), true, hypothesis.proof)), hypothesis.instance, Equation.Operation.LESS_OR_EQUALS, terms.term2, terms.term1, terms.lcm));
      } else {
        result.add(new Hypothesis<>(hypothesis.proof, hypothesis.instance, hypothesis.operation, terms.term1, terms.term2, terms.lcm));
      }
    }
  }

  private ConcreteExpression equationToConcrete(Equation<CompiledTerm> equation) {
    CoreConstructor constructor = switch (equation.operation) {
      case LESS -> ext.linearSolverMeta.less;
      case LESS_OR_EQUALS -> ext.linearSolverMeta.lessOrEquals;
      case EQUALS -> ext.linearSolverMeta.equals;
    };
    return factory.tuple(equation.lhsTerm.concrete(), factory.ref(constructor.getRef()), equation.rhsTerm.concrete());
  }

  private ConcreteExpression equationsToConcrete(List<? extends Hypothesis<CompiledTerm>> equations) {
    ConcreteExpression result = factory.ref(ext.prelude.getEmptyArray().getRef());
    for (int i = equations.size() - 1; i >= 0; i--) {
      result = factory.app(factory.ref(ext.prelude.getArrayCons().getRef()), true, equationToConcrete(equations.get(i)), result);
    }
    return result;
  }

  private ConcreteExpression witnessesToConcrete(List<? extends Hypothesis<CompiledTerm>> hypotheses) {
    ConcreteExpression result = factory.ref(ext.prelude.getEmptyArray().getRef());
    for (int i = hypotheses.size() - 1; i >= 0; i--) {
      if (hypotheses.get(i).proof != null) {
        result = factory.app(factory.ref(ext.prelude.getArrayCons().getRef()), true, hypotheses.get(i).proof, result);
      }
    }
    return result;
  }

  private ConcreteExpression certificateToConcrete(List<BigInteger> certificate, List<Equation<CompiledTerm>> equations) {
    assert certificate.size() == equations.size();
    ConcreteExpression result = factory.ref(ext.prelude.getEmptyArray().getRef());
    for (int i = certificate.size() - 1; i >= 1; i--) {
      result = factory.app(factory.ref(ext.prelude.getArrayCons().getRef()), true, factory.number(certificate.get(i).multiply(equations.get(i).getLCM())), result);
    }
    return factory.tuple(result, factory.number(certificate.get(0)), factory.ref(ext.prelude.getIdp().getRef()), factory.app(factory.ref(ext.prelude.getIdp().getRef()), factory.arg(factory.ref(ext.Bool.getRef()), false), factory.arg(factory.ref(ext.true_.getRef()), false)));
  }

  private <E> void removeUnusedVariables(List<Hypothesis<CompiledTerm>> hypotheses, List<E> values) {
    Set<Integer> vars = new HashSet<>();
    for (Hypothesis<CompiledTerm> hypothesis : hypotheses) {
      vars.addAll(hypothesis.lhsTerm.vars());
      vars.addAll(hypothesis.rhsTerm.vars());
    }
    for (int i = 0; i < values.size(); i++) {
      if (!vars.contains(i)) {
        values.set(i, null);
      }
    }
  }

  private ConcreteExpression makeData(CoreClassCallExpression classCall, ConcreteExpression instanceArg, RingKind kind, List<CoreExpression> valueList) {
    boolean isRing = kind != RingKind.NAT && kind != RingKind.NONE || classCall.getDefinition().isSubClassOf(ext.equationMeta.OrderedRing);
    ConcreteExpression varsArg = factory.ref(ext.prelude.getEmptyArray().getRef());
    for (int i = valueList.size() - 1; i >= 0; i--) {
      varsArg = factory.app(factory.ref(ext.prelude.getArrayCons().getRef()), true, valueList.get(i) == null ? factory.ref(ext.zro.getRef()) : factory.core(valueList.get(i).computeTyped()), varsArg);
    }
    return factory.newExpr(factory.classExt(factory.ref((kind == RingKind.RAT_ALG ? ext.linearSolverMeta.LinearRatAlgebraData : kind == RingKind.RAT ? ext.linearSolverMeta.LinearRatData : isRing ? ext.linearSolverMeta.LinearRingData : ext.linearSolverMeta.LinearSemiringData).getRef()), Arrays.asList(factory.implementation((ext.equationMeta.RingDataCarrier).getRef(), instanceArg), factory.implementation(ext.equationMeta.DataFunction.getRef(), varsArg))));
  }

  private Equation<CompiledTerm> makeZeroLessOne(CoreExpression instance) {
    return new Equation<>(instance, Equation.Operation.LESS, new CompiledTerm(null, Collections.emptyList(), Collections.emptySet()), new CompiledTerm(null, Collections.singletonList(BigInteger.ONE), Collections.emptySet()));
  }

  private void makeZeroLessVar(CoreExpression instance, TermCompiler compiler, List<Hypothesis<CompiledTerm>> result) {
    for (int i = 1; i <= compiler.getNumberOfVariables() ; i++) {
      if (!compiler.isNat() && !compiler.positiveVars.contains(i - 1)) {
        continue;
      }
      List<BigInteger> coefs = new ArrayList<>(i + 1);
      for (int j = 0; j < i; j++) {
        coefs.add(BigInteger.ZERO);
      }
      coefs.add(BigInteger.ONE);
      ConcreteExpression proof = factory.ref(ext.equationMeta.zeroLE_.getRef());
      if (compiler.getKind().ordinal() > RingKind.NAT.ordinal()) {
        proof = factory.app(factory.ref(ext.linearSolverMeta.posLEpos.getRef()), true, proof);
      }
      if (compiler.getKind() != RingKind.NONE) {
        if (compiler.getKind().ordinal() > RingKind.INT.ordinal()) {
          proof = factory.app(factory.ref(ext.linearSolverMeta.fromIntLE.getRef()), true, proof);
        }
        if (compiler.getKind().ordinal() > RingKind.RAT.ordinal()) {
          proof = factory.app(factory.ref(ext.linearSolverMeta.fromIntLE.getRef()), true, proof);
        }
      }
      int var = i - 1;
      result.add(new Hypothesis<>(proof, instance, Equation.Operation.LESS_OR_EQUALS, new CompiledTerm(factory.ref(ext.equationMeta.zroTerm.getRef()), Collections.emptyList(), Collections.emptySet()), new CompiledTerm(factory.app(factory.ref(ext.equationMeta.varTerm.getRef()), true, factory.number(var)), coefs, Collections.singleton(var)), BigInteger.ONE));
    }
  }

  private Hypothesis<CoreExpression> natToIntHypothesis(Hypothesis<CoreExpression> rule, CoreExpression instance) {
    CoreExpression newLHS = TermCompiler.toPos(rule.lhsTerm, typechecker, factory, ext);
    CoreExpression newRHS = TermCompiler.toPos(rule.rhsTerm, typechecker, factory, ext);
    return newLHS == null || newRHS == null ? null : new Hypothesis<>(rule.operation == Equation.Operation.EQUALS ? factory.app(factory.ref(ext.pmap.getRef()), true, factory.ref(ext.prelude.getPos().getRef()), rule.proof) : factory.app(factory.ref(rule.operation == Equation.Operation.LESS ? ext.linearSolverMeta.posLpos.getRef() : ext.linearSolverMeta.posLEpos.getRef()), true, rule.proof), instance, rule.operation, newLHS, newRHS, rule.lcm);
  }

  private Hypothesis<CoreExpression> intToRatHypothesis(Hypothesis<CoreExpression> rule, CoreExpression instance) {
    CoreExpression newLHS = TermCompiler.toRat(rule.lhsTerm, typechecker, factory, ext);
    CoreExpression newRHS = TermCompiler.toRat(rule.rhsTerm, typechecker, factory, ext);
    return newLHS == null || newRHS == null ? null : new Hypothesis<>(rule.operation == Equation.Operation.EQUALS ? factory.app(factory.ref(ext.pmap.getRef()), true, factory.ref(ext.equationMeta.fromInt.getRef()), rule.proof) : factory.app(factory.ref(rule.operation == Equation.Operation.LESS ? ext.linearSolverMeta.fromIntL.getRef() : ext.linearSolverMeta.fromIntLE.getRef()), true, rule.proof), instance, rule.operation, newLHS, newRHS, rule.lcm);
  }

  private Hypothesis<CoreExpression> ratToRatAlgebraHypothesis(Hypothesis<CoreExpression> rule, CoreExpression instance) {
    CoreExpression newLHS = TermCompiler.toRatAlgebra(rule.lhsTerm, typechecker, factory, ext);
    CoreExpression newRHS = TermCompiler.toRatAlgebra(rule.rhsTerm, typechecker, factory, ext);
    return newLHS == null || newRHS == null ? null : new Hypothesis<>(rule.operation == Equation.Operation.EQUALS ? factory.app(factory.ref(ext.pmap.getRef()), true, factory.ref(ext.linearSolverMeta.coefMap.getRef()), rule.proof) : factory.app(factory.ref(rule.operation == Equation.Operation.LESS ? ext.linearSolverMeta.coefMapL.getRef() : ext.linearSolverMeta.coefMapLE.getRef()), true, rule.proof), instance, rule.operation, newLHS, newRHS, rule.lcm);
  }

  private Hypothesis<CoreExpression> convertHypothesis(Hypothesis<CoreExpression> rule, CoreExpression instance, RingKind from, RingKind to) {
    if (from == RingKind.RAT_ALG || to == RingKind.NAT) return rule;
    if (from == RingKind.NAT) {
      rule = natToIntHypothesis(rule, instance);
      if (rule == null) return null;
      from = RingKind.INT;
    }
    if (from == RingKind.INT) {
      if (to == RingKind.INT) return rule;
      rule = intToRatHypothesis(rule, instance);
      if (rule == null) return null;
      from = RingKind.RAT;
    }
    if (from == RingKind.RAT) {
      if (to == RingKind.RAT) return rule;
      rule = ratToRatAlgebraHypothesis(rule, instance);
    }
    return rule;
  }

  private void dropUnusedHypotheses(List<BigInteger> solution, List<?> list) {
    assert solution.size() == list.size();
    for (int i = solution.size() - 1; i >= 0; i--) {
      if (solution.get(i).equals(BigInteger.ZERO)) {
        list.remove(i);
      }
    }
  }

  public TypedExpression solve(CoreExpression expectedType, ConcreteExpression hint) {
    expectedType = expectedType.normalize(NormalizationMode.WHNF);
    Equation<CoreExpression> resultEquation;
    if (expectedType instanceof CoreDataCallExpression && ((CoreDataCallExpression) expectedType).getDefinition() == ext.Empty) {
      resultEquation = null;
    } else {
      resultEquation = typeToEquation(expectedType, null, true);
      if (resultEquation == null) return null;
    }

    List<Hypothesis<CoreExpression>> rules = new ArrayList<>();
    ContextHelper helper = new ContextHelper(hint);
    for (CoreBinding binding : helper.getAllBindings(typechecker)) {
      Hypothesis<CoreExpression> hypothesis = bindingToHypothesis(binding);
      if (hypothesis != null) rules.add(hypothesis);
    }

    if (resultEquation != null) {
      TypedExpression instance = resultEquation.instance.computeTyped();
      CoreClassCallExpression classCall = Utils.getClassCall(instance.getType());
      TermCompiler compiler = makeTermCompiler(instance, classCall);
      if (compiler != null) {
        List<Hypothesis<CoreExpression>> newRules = new ArrayList<>();
        for (Hypothesis<CoreExpression> rule : rules) {
          if (rule.instance.compare(resultEquation.instance, CMP.EQ)) {
            newRules.add(rule);
          } else {
            Hypothesis<CoreExpression> newRule = convertHypothesis(rule, resultEquation.instance, BaseTermCompiler.getTermCompilerKind(rule.instance, ext.equationMeta), compiler.getKind());
            if (newRule != null) {
              newRules.add(newRule);
            }
          }
        }
        rules = newRules;
        CoreFunctionDefinition function;
        List<Hypothesis<CompiledTerm>> compiledRules = new ArrayList<>();
        compileHypotheses(compiler, rules, compiledRules);
        List<List<Equation<CompiledTerm>>> rulesSet = new ArrayList<>(2);
        List<Equation<CompiledTerm>> compiledRules1 = new ArrayList<>();
        compiledRules1.add(makeZeroLessOne(instance.getExpression()));
        rulesSet.add(compiledRules1);
        CompiledTerms compiledResults = compiler.compileTerms(resultEquation.lhsTerm, resultEquation.rhsTerm);
        if (compiler.isNat() || !compiler.positiveVars.isEmpty()) {
          makeZeroLessVar(instance.getExpression(), compiler, compiledRules);
        }
        switch (resultEquation.operation) {
          case LESS -> {
            compiledRules1.add(new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS_OR_EQUALS, compiledResults.term2, compiledResults.term1, compiledResults.lcm));
            function = ext.linearSolverMeta.solveLessProblem;
          }
          case LESS_OR_EQUALS -> {
            compiledRules1.add(new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS, compiledResults.term2, compiledResults.term1, compiledResults.lcm));
            function = ext.linearSolverMeta.solveLeqProblem;
          }
          case EQUALS -> {
            List<Equation<CompiledTerm>> compiledRules2 = new ArrayList<>(compiledRules1);
            compiledRules1.add(new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS, compiledResults.term1, compiledResults.term2, compiledResults.lcm));
            compiledRules2.add(new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS, compiledResults.term2, compiledResults.term1, compiledResults.lcm));
            compiledRules2.addAll(compiledRules);
            rulesSet.add(compiledRules2);
            function = ext.linearSolverMeta.solveEqProblem;
          }
          default -> throw new IllegalStateException();
        }
        compiledRules1.addAll(compiledRules);
        List<List<BigInteger>> solutions = new ArrayList<>(rulesSet.size());
        for (List<Equation<CompiledTerm>> equations : rulesSet) {
          List<BigInteger> solution = solveEquations(equations, compiler.getNumberOfVariables());
          if (solution != null) solutions.add(solution);
        }
        if (solutions.size() == rulesSet.size()) {
          List<BigInteger> combinedSolutions = new ArrayList<>();
          for (List<BigInteger> solution : solutions) {
            for (int i = combinedSolutions.size() + 2; i < solution.size(); i++) {
              combinedSolutions.add(BigInteger.ZERO);
            }
            for (int i = 0; i < solution.size() - 2; i++) {
              combinedSolutions.set(i, combinedSolutions.get(i).max(solution.get(i + 2)));
            }
          }
          dropUnusedHypotheses(combinedSolutions, compiledRules);
          List<CoreExpression> values = compiler.getValues().getValues();
          List<Hypothesis<CompiledTerm>> newCompiledRules = new ArrayList<>(compiledRules);
          newCompiledRules.add(new Hypothesis<>(null, null, null, compiledResults.term1, compiledResults.term2, BigInteger.ONE));
          removeUnusedVariables(newCompiledRules, values);
          ConcreteAppBuilder builder = factory.appBuilder(factory.ref(function.getRef()))
            .app(makeData(classCall, factory.core(instance), compiler.getKind(), values), false)
            .app(equationsToConcrete(compiledRules))
            .app(compiledResults.term1.concrete())
            .app(compiledResults.term2.concrete());
          for (int i = 0; i < solutions.size(); i++) {
            dropUnusedHypotheses(combinedSolutions, solutions.get(i).subList(2, solutions.get(i).size()));
            dropUnusedHypotheses(combinedSolutions, rulesSet.get(i).subList(2, rulesSet.get(i).size()));
            builder.app(certificateToConcrete(solutions.get(i), rulesSet.get(i)));
          }
          return typechecker.typecheck(builder.app(witnessesToConcrete(compiledRules)).build(), null);
        }
      }
    } else {
      List<Hypothesis<CoreExpression>> finalRules = rules;
      boolean[] solutionFound = new boolean[] { false };
      TypedExpression result = typechecker.withCurrentState(tc -> {
        List<List<Hypothesis<CoreExpression>>> rulesSet = new ArrayList<>();
        for (Hypothesis<CoreExpression> rule : finalRules) {
          RingKind kind = BaseTermCompiler.getTermCompilerKind(rule.instance, ext.equationMeta);
          boolean found = false;
          for (int i = 0; i < rulesSet.size(); i++) {
            List<Hypothesis<CoreExpression>> newRules = rulesSet.get(i);
            Boolean compareResult = Utils.tryWithSavedState(tc, tc2 -> tc2.compare(rule.instance, newRules.get(0).instance, CMP.EQ, marker, false, true, false));
            if (compareResult != null && compareResult) {
              newRules.add(rule);
              found = true;
              break;
            } else if (kind != RingKind.NAT) {
              RingKind newKind = BaseTermCompiler.getTermCompilerKind(newRules.get(0).instance, ext.equationMeta);
              if (kind == RingKind.NONE && newKind != RingKind.RAT || newKind == RingKind.NONE || kind.ordinal() > newKind.ordinal() && !(newKind == RingKind.RAT && kind == RingKind.NONE)) {
                found = true;
                List<Hypothesis<CoreExpression>> newRules2 = new ArrayList<>(newRules.size() + 1);
                boolean remove = true;
                for (Hypothesis<CoreExpression> newRule : newRules) {
                  Hypothesis<CoreExpression> newRule2 = convertHypothesis(newRule, rule.instance, newKind, kind);
                  if (newRule2 != null) {
                    newRules2.add(newRule2);
                  } else {
                    remove = false;
                  }
                }
                newRules2.add(rule);
                rulesSet.add(newRules2);
                if (remove) {
                  rulesSet.remove(i);
                }
                break;
              }
            }
          }
          if (!found) {
            List<Hypothesis<CoreExpression>> newRules = new ArrayList<>();
            newRules.add(rule);
            rulesSet.add(newRules);
          }
        }
        for (List<Hypothesis<CoreExpression>> equations : rulesSet) {
          TypedExpression instance = equations.get(0).instance.computeTyped();
          CoreClassCallExpression classCall = Utils.getClassCall(instance.getType());
          TermCompiler compiler = makeTermCompiler(instance, classCall);
          if (compiler == null) continue;
          List<Hypothesis<CompiledTerm>> compiledEquations = new ArrayList<>();
          compileHypotheses(compiler, equations, compiledEquations);
          if (compiler.isNat() || compiler.isInt()) {
            makeZeroLessVar(instance.getExpression(), compiler, compiledEquations);
          }
          List<Equation<CompiledTerm>> compiledEquations1 = new ArrayList<>(compiledEquations.size() + 1);
          compiledEquations1.add(makeZeroLessOne(instance.getExpression()));
          compiledEquations1.addAll(compiledEquations);
          List<BigInteger> solution = solveEquations(compiledEquations1, compiler.getNumberOfVariables());
          if (solution != null) {
            List<BigInteger> subList = solution.subList(1, solution.size());
            dropUnusedHypotheses(subList, compiledEquations);
            dropUnusedHypotheses(subList, compiledEquations1.subList(1, compiledEquations1.size()));
            dropUnusedHypotheses(subList, subList);
            solutionFound[0] = true;
            List<CoreExpression> values = compiler.getValues().getValues();
            removeUnusedVariables(compiledEquations, values);
            return tc.typecheck(factory.appBuilder(factory.ref(ext.linearSolverMeta.solveContrProblem.getRef()))
              .app(makeData(classCall, factory.core(instance), compiler.getKind(), values), false)
              .app(equationsToConcrete(compiledEquations))
              .app(certificateToConcrete(solution, compiledEquations1))
              .app(witnessesToConcrete(compiledEquations))
              .build(), null);
          }
        }
        return null;
      });
      if (solutionFound[0]) {
        return result;
      }
    }

    errorReporter.report(new LinearSolverError(typechecker.getExpressionPrettifier(), resultEquation, rules, marker));
    return null;
  }
}
