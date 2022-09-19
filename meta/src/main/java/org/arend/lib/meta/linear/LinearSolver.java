package org.arend.lib.meta.linear;

import org.arend.ext.concrete.ConcreteAppBuilder;
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

    if (relationData.defCall.getDefinition() == ext.equationMeta.linearOrederLeq) {
      return new Equation<>(relationData.defCall.getDefCallArguments().get(0), Equation.Operation.LESS_OR_EQUALS, relationData.leftExpr, relationData.rightExpr);
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

        boolean swap = cmp1 > 0;
        if (!(equation1.operation == Equation.Operation.EQUALS && equation2.operation == Equation.Operation.EQUALS)) {
          if (equation1.operation != Equation.Operation.EQUALS && equation2.operation != Equation.Operation.EQUALS) {
            if (!(cmp1 < 0 && cmp2 > 0 || cmp1 > 0 && cmp2 < 0)) {
              continue;
            }
          } else if (equation2.operation != Equation.Operation.EQUALS) {
            if (!(cmp1 < 0 && cmp2 > 0 || cmp1 > 0 && cmp2 < 0)) {
              equation1 = new Equation<>(equation1.instance, Equation.Operation.EQUALS, equation1.rhsTerm, equation1.lhsTerm);
              swap = !swap;
            }
          } else {
            if (!(cmp1 < 0 && cmp2 > 0 || cmp1 > 0 && cmp2 < 0)) {
              equation2 = new Equation<>(equation2.instance, Equation.Operation.EQUALS, equation2.rhsTerm, equation2.lhsTerm);
            }
          }
          if (swap) {
            Equation<CompiledTerm> tmp = equation1;
            equation1 = equation2;
            equation2 = tmp;
          }
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
          new CompiledTerm(null, lhs), new CompiledTerm(null, rhs)));
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

  private TermCompiler makeTermCompiler(TypedExpression instance) {
    CoreClassCallExpression classCall = Utils.getClassCall(instance.getType());
    return classCall == null ? null : new TermCompiler(classCall, instance, ext, typechecker, marker);
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

  private ConcreteExpression makeData(ConcreteExpression instanceArg, List<CoreExpression> valueList) {
    ConcreteExpression varsArg = factory.ref(ext.prelude.getEmptyArray().getRef());
    for (int i = valueList.size() - 1; i >= 0; i--) {
      varsArg = factory.app(factory.ref(ext.prelude.getArrayCons().getRef()), true, factory.core(null, valueList.get(i).computeTyped()), varsArg);
    }
    return factory.newExpr(factory.classExt(factory.ref(ext.linearSolverMeta.SemiringData.getRef()), Arrays.asList(factory.implementation((ext.equationMeta.RingDataCarrier).getRef(), instanceArg), factory.implementation(ext.equationMeta.DataFunction.getRef(), varsArg))));
  }

  private Equation<CompiledTerm> makeZeroLessOne(CoreExpression instance) {
    return new Equation<>(instance, Equation.Operation.LESS, new CompiledTerm(null, Collections.emptyList()), new CompiledTerm(null, Collections.singletonList(BigInteger.ONE)));
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
      TypedExpression instance = resultEquation.instance.computeTyped();
      TermCompiler compiler = makeTermCompiler(instance);
      if (compiler != null) {
        CoreFunctionDefinition function;
        List<Hypothesis<CompiledTerm>> compiledRules = compileHypotheses(compiler, newRules);
        List<List<Equation<CompiledTerm>>> rulesSet = new ArrayList<>(2);
        List<Equation<CompiledTerm>> compiledRules1 = new ArrayList<>();
        rulesSet.add(compiledRules1);
        CompiledTerm compiledResultLhs = compiler.compileTerm(resultEquation.lhsTerm);
        CompiledTerm compiledResultRhs = compiler.compileTerm(resultEquation.rhsTerm);
        switch (resultEquation.operation) {
          case LESS:
            compiledRules1.add(new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS_OR_EQUALS, compiledResultRhs, compiledResultLhs));
            function = ext.linearSolverMeta.solveLessHProblem;
            break;
          case LESS_OR_EQUALS:
            compiledRules1.add(new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS, compiledResultRhs, compiledResultLhs));
            function = ext.linearSolverMeta.solveLeqHProblem;
            break;
          case EQUALS: {
            List<Equation<CompiledTerm>> compiledRules2 = new ArrayList<>();
            compiledRules1.add(new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS, compiledResultLhs, compiledResultRhs));
            compiledRules2.add(new Hypothesis<>(null, resultEquation.instance, Equation.Operation.LESS, compiledResultRhs, compiledResultLhs));
            compiledRules2.add(makeZeroLessOne(instance.getExpression()));
            compiledRules2.addAll(compiledRules);
            rulesSet.add(compiledRules2);
            function = ext.linearSolverMeta.solveEqHProblem;
            break;
          }
          default:
            throw new IllegalStateException();
        }
        compiledRules1.add(makeZeroLessOne(instance.getExpression()));
        compiledRules1.addAll(compiledRules);
        List<List<BigInteger>> solutions = new ArrayList<>(rulesSet.size());
        for (List<Equation<CompiledTerm>> equations : rulesSet) {
          List<BigInteger> solution = solveEquations(equations, compiler.getNumberOfVariables());
          if (solution != null) solutions.add(solution);
        }
        if (solutions.size() == rulesSet.size()) {
          ConcreteAppBuilder builder = factory.appBuilder(factory.ref(function.getRef()))
            .app(makeData(factory.core(instance), compiler.getValues().getValues()), false)
            .app(equationsToConcrete(compiledRules))
            .app(compiledResultLhs.concrete)
            .app(compiledResultRhs.concrete);
          for (List<BigInteger> solution : solutions) {
            builder.app(certificateToConcrete(solution));
          }
          return typechecker.typecheck(builder.app(witnessesToConcrete(compiledRules)).build(), null);
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
        TypedExpression instance = equations.get(0).instance.computeTyped();
        TermCompiler compiler = makeTermCompiler(instance);
        if (compiler == null) continue;
        List<Hypothesis<CompiledTerm>> compiledEquations = compileHypotheses(compiler, equations);
        List<Equation<CompiledTerm>> compiledEquations1 = new ArrayList<>(compiledEquations.size() + 1);
        compiledEquations1.add(makeZeroLessOne(instance.getExpression()));
        compiledEquations1.addAll(compiledEquations);
        List<BigInteger> solution = solveEquations(compiledEquations1, compiler.getNumberOfVariables());
        if (solution != null) {
          return typechecker.typecheck(factory.appBuilder(factory.ref(ext.linearSolverMeta.solveContrHProblem.getRef()))
            .app(makeData(factory.core(instance), compiler.getValues().getValues()), false)
            .app(equationsToConcrete(compiledEquations))
            .app(certificateToConcrete(solution))
            .app(witnessesToConcrete(compiledEquations))
            .build(), null);
        }
      }
    }

    errorReporter.report(new LinearSolverError(resultEquation == null, rules, marker));
    return null;
  }
}
