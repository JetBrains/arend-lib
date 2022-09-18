package org.arend.lib.meta.linear;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.InstanceInferenceError;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.error.LinearSolverError;
import org.arend.lib.error.TypeError;
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

  private CoreExpression findInstance(CoreExpression type, boolean reportError) {
    TypedExpression instance = typechecker.findInstance(ext.equationMeta.LinearlyOrderedSemiring, type, null, marker);
    if (instance == null) {
      if (reportError) errorReporter.report(new InstanceInferenceError(ext.equationMeta.LinearlyOrderedSemiring.getRef(), type, marker));
      return null;
    }
    return instance.getExpression();
  }

  private void reportTypeError(CoreExpression expectedType) {
    typechecker.getErrorReporter().report(new TypeError("The expected type should be either an equation or the empty type", expectedType, marker));
  }

  private Equation<CoreExpression> typeToEquation(CoreExpression type, boolean reportError) {
    CoreFunCallExpression eq = type.toEquality();
    if (eq != null) {
      CoreExpression instance = findInstance(eq.getDefCallArguments().get(0), reportError);
      if (instance == null) return null;
      return new Equation<>(instance, Equation.Operation.EQUALS, eq.getDefCallArguments().get(1), eq.getDefCallArguments().get(2));
    }

    RelationData relationData = RelationData.getRelationData(type.normalize(NormalizationMode.WHNF));
    if (relationData == null) {
      if (reportError) reportTypeError(type);
      return null;
    }
    if (relationData.defCall instanceof CoreFieldCallExpression) {
      CoreClassField field = ((CoreFieldCallExpression) relationData.defCall).getDefinition();
      if (field == ext.equationMeta.less || field == ext.equationMeta.lessOrEquals) {
        return new Equation<>(((CoreFieldCallExpression) relationData.defCall).getArgument(), field == ext.equationMeta.less ? Equation.Operation.LESS : Equation.Operation.LESS_OR_EQUALS, relationData.leftExpr, relationData.rightExpr);
      }
      if (reportError) reportTypeError(type);
      return null;
    }

    var pair = instanceCache.computeIfAbsent(relationData.defCall.getDefinition(), def -> {
      DefImplInstanceSearchParameters parameters = new DefImplInstanceSearchParameters(def) {
        @Override
        protected List<CoreClassField> getRelationFields(CoreClassDefinition classDef) {
          return classDef.isSubClassOf(ext.equationMeta.LinearlyOrderedSemiring) ? Arrays.asList(ext.equationMeta.less, ext.equationMeta.lessOrEquals) : Collections.emptyList();
        }
      };
      TypedExpression instance = typechecker.findInstance(parameters, null, null, marker);
      return instance == null ? null : new Pair<>(instance, parameters.getRelationField());
    });
    if (pair == null) {
      if (reportError) reportTypeError(type);
      return null;
    }
    return new Equation<>(pair.proj1.getExpression(), pair.proj2 == ext.equationMeta.less ? Equation.Operation.LESS : Equation.Operation.LESS_OR_EQUALS, relationData.leftExpr, relationData.rightExpr);
  }

  private static class Hypothesis<E> extends Equation<E> {
    public final ConcreteExpression binding;

    private Hypothesis(ConcreteExpression binding, CoreExpression instance, Operation operation, E lhsTerm, E rhsTerm) {
      super(instance, operation, lhsTerm, rhsTerm);
      this.binding = binding;
    }
  }

  private Hypothesis<CoreExpression> bindingToHypothesis(CoreBinding binding) {
    if (binding == null) return null;
    Equation<CoreExpression> equation = typeToEquation(binding.getTypeExpr().normalize(NormalizationMode.WHNF), false);
    return equation == null ? null : new Hypothesis<>(factory.ref(binding), equation.instance, equation.operation, equation.lhsTerm, equation.rhsTerm);
  }

  private List<BigInteger> solveEquations(List<? extends Equation<CompiledTerm>> equations, int var) {
  }

  private TermCompiler makeTermCompiler(CoreExpression instance) {
    TypedExpression typedInstance = instance.computeTyped();
    CoreClassCallExpression classCall = Utils.getClassCall(typedInstance.getType());
    return classCall == null ? null : new TermCompiler(classCall, typedInstance, ext, typechecker, marker);
  }

  private static Hypothesis<CompiledTerm> compileHypothesis(TermCompiler compiler, Hypothesis<CoreExpression> hypothesis) {
    return new Hypothesis<>(hypothesis.binding, hypothesis.instance, hypothesis.operation, compiler.compileTerm(hypothesis.lhsTerm), compiler.compileTerm(hypothesis.rhsTerm));
  }

  private static List<Hypothesis<CompiledTerm>> compileHypotheses(TermCompiler compiler, List<Hypothesis<CoreExpression>> equations) {
    List<Hypothesis<CompiledTerm>> result = new ArrayList<>(equations.size());
    for (Hypothesis<CoreExpression> hypothesis : equations) {
      result.add(compileHypothesis(compiler, hypothesis));
    }
    return result;
  }

  private ConcreteExpression equationToConcrete(Equation<CompiledTerm> equation) {
    CoreConstructor constructor;
    switch (equation.operation) {
      case LESS: constructor = ext.linearSolverMeta.less; break;
      case LESS_OR_EQUALS: constructor = ext.linearSolverMeta.lessOrEquals; break;
      case EQUALS: constructor = ext.linearSolverMeta.equals; break;
      default: throw new IllegalStateException();
    }
    return factory.tuple(equation.lhsTerm.concrete, factory.ref(constructor.getRef()), equation.rhsTerm.concrete);
  }

  private ConcreteExpression equationsToConcrete(List<? extends Equation<CompiledTerm>> equations) {
    ConcreteExpression result = factory.ref(ext.prelude.getEmptyArray().getRef());
    for (int i = equations.size() - 1; i >= 0; i--) {
      result = factory.app(factory.ref(ext.prelude.getArrayCons().getRef()), true, equationToConcrete(equations.get(i)), result);
    }
    return result;
  }

  private ConcreteExpression witnessesToConcrete(List<? extends Hypothesis<CompiledTerm>> hypotheses) {
    ConcreteExpression result = factory.ref(ext.prelude.getEmptyArray().getRef());
    for (int i = hypotheses.size() - 1; i >= 0; i--) {
      if (hypotheses.get(i).binding != null) {
        result = factory.app(factory.ref(ext.prelude.getArrayCons().getRef()), true, hypotheses.get(i).binding, result);
      }
    }
    return result;
  }

  private ConcreteExpression certificateToConcrete(List<BigInteger> certificate) {
    ConcreteExpression result = factory.ref(ext.prelude.getEmptyArray().getRef());
    for (int i = certificate.size() - 1; i >= 0; i--) {
      result = factory.app(factory.ref(ext.prelude.getArrayCons().getRef()), true, factory.number(certificate.get(i)), result);
    }
    return factory.tuple(result, factory.ref(ext.prelude.getIdp().getRef()), factory.ref(ext.prelude.getIdp().getRef()));
  }

  public TypedExpression solve(CoreExpression expectedType, ConcreteExpression hint) {
    expectedType = expectedType.normalize(NormalizationMode.WHNF);
    Equation<CoreExpression> resultEquation;
    if (expectedType instanceof CoreDataCallExpression && ((CoreDataCallExpression) expectedType).getDefinition() == ext.Empty) {
      resultEquation = null;
    } else {
      resultEquation = typeToEquation(expectedType, true);
      if (resultEquation == null) return null;
    }

    List<Hypothesis<CoreExpression>> rules = new ArrayList<>();
    ContextHelper helper = new ContextHelper(hint);
    for (CoreBinding binding : helper.getAllBindings(typechecker)) {
      Hypothesis<CoreExpression> hypothesis = bindingToHypothesis(binding);
      if (hypothesis != null) rules.add(hypothesis);
    }

    if (resultEquation != null) {
      List<Hypothesis<CoreExpression>> newRules = new ArrayList<>();
      for (Hypothesis<CoreExpression> rule : rules) {
        if (rule.instance.compare(resultEquation.instance, CMP.EQ)) {
          newRules.add(rule);
        }
      }
      TermCompiler compiler = makeTermCompiler(resultEquation.instance);
      if (compiler != null) {
        CoreFunctionDefinition function;
        List<Hypothesis<CompiledTerm>> compiledRules = compileHypotheses(compiler, newRules);
        List<List<Hypothesis<CompiledTerm>>> rulesSet = new ArrayList<>(2);
        List<Hypothesis<CompiledTerm>> compiledRules1 = new ArrayList<>(compiledRules);
        rulesSet.add(compiledRules1);
        CompiledTerm compiledResultLhs = compiler.compileTerm(resultEquation.lhsTerm);
        CompiledTerm compiledResultRhs = compiler.compileTerm(resultEquation.rhsTerm);
        switch (resultEquation.operation) {
          case LESS:
            compiledRules1.add(0, new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS_OR_EQUALS, compiledResultRhs, compiledResultLhs));
            function = ext.linearSolverMeta.solveLessHProblem;
            break;
          case LESS_OR_EQUALS:
            compiledRules1.add(0, new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS, compiledResultRhs, compiledResultLhs));
            function = ext.linearSolverMeta.solveLeqHProblem;
            break;
          case EQUALS: {
            List<Hypothesis<CompiledTerm>> compiledRules2 = new ArrayList<>(compiledRules);
            compiledRules1.add(0, new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS, compiledResultLhs, compiledResultRhs));
            compiledRules2.add(0, new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS, compiledResultRhs, compiledResultLhs));
            rulesSet.add(compiledRules2);
            function = ext.linearSolverMeta.solveEqHProblem;
            break;
          }
          default:
            throw new IllegalStateException();
        }
        List<List<BigInteger>> solutions = new ArrayList<>(rulesSet.size());
        for (List<Hypothesis<CompiledTerm>> equations : rulesSet) {
          List<BigInteger> solution = solveEquations(equations, compiler.getNumberOfVariables() - 1);
          if (solution != null) solutions.add(solution);
        }
        if (solutions.size() == rulesSet.size()) {
          List<ConcreteExpression> args = new ArrayList<>(6);
          args.add(equationsToConcrete(compiledRules));
          args.add(compiledResultLhs.concrete);
          args.add(compiledResultRhs.concrete);
          for (List<BigInteger> solution : solutions) {
            args.add(certificateToConcrete(solution));
          }
          args.add(witnessesToConcrete(compiledRules));
          return typechecker.typecheck(factory.app(factory.ref(function.getRef()), true, args), null);
        }
      }
    } else {
      List<List<Hypothesis<CoreExpression>>> rulesSet = new ArrayList<>();
      for (Hypothesis<CoreExpression> rule : rules) {
        boolean found = false;
        for (List<Hypothesis<CoreExpression>> newRules : rulesSet) {
          if (rule.instance.compare(newRules.get(0).instance, CMP.EQ)) {
            newRules.add(rule);
            found = true;
            break;
          }
        }
        if (!found) {
          List<Hypothesis<CoreExpression>> newRules = new ArrayList<>();
          newRules.add(rule);
          rulesSet.add(newRules);
        }
      }
      for (List<Hypothesis<CoreExpression>> equations : rulesSet) {
        TermCompiler compiler = makeTermCompiler(equations.get(0).instance);
        if (compiler == null) continue;
        List<Hypothesis<CompiledTerm>> compiledEquations = compileHypotheses(compiler, equations);
        List<BigInteger> solution = solveEquations(compiledEquations, compiler.getNumberOfVariables() - 1);
        if (solution != null) {
          return typechecker.typecheck(factory.app(factory.ref(ext.linearSolverMeta.solveContrHProblem.getRef()), true, equationsToConcrete(compiledEquations), certificateToConcrete(solution), witnessesToConcrete(compiledEquations)), null);
        }
      }
    }

    errorReporter.report(new LinearSolverError(resultEquation == null, rules, marker));
    return null;
  }
}
