package org.arend.lib.meta;

import org.arend.ext.concrete.*;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteCaseExpression;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteLamExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreDataDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.context.Context;
import org.arend.lib.context.HidingContext;
import org.arend.lib.error.TypeError;
import org.arend.lib.key.FieldKey;
import org.arend.lib.meta.closure.BinaryRelationClosure;
import org.arend.lib.meta.closure.BunchedEquivalenceClosure;
import org.arend.lib.meta.closure.ValuesRelationClosure;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;

public class ContradictionMeta extends BaseMetaDefinition {
  public final StdExtension ext;

  public ContradictionMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    return checkCore(contextData.getArguments().isEmpty() ? null : contextData.getArguments().get(0).getExpression(), contextData.getExpectedType(), contextData.getExpectedType() != null, contextData.getMarker(), typechecker);
  }

  private static class RType {
    final CoreBinding binding;
    final CoreExpression type;

    RType(CoreBinding binding, CoreExpression type) {
      this.binding = binding;
      this.type = type;
    }
  }

  private static class EqType extends RType {
    final CoreExpression leftExpr;
    final CoreExpression rightExpr;

    EqType(CoreBinding binding, CoreFunCallExpression eqType, CoreExpression leftExpr, CoreExpression rightExpr) {
      super(binding, eqType);
      this.leftExpr = leftExpr;
      this.rightExpr = rightExpr;
    }
  }

  private static class Negation {
    final List<RType> assumptions;
    final CoreExpression type;
    final Function<Deque<ConcreteExpression>, ConcreteExpression> proof;

    private Negation(List<RType> assumptions, CoreExpression type, Function<Deque<ConcreteExpression>, ConcreteExpression> proof) {
      this.assumptions = assumptions;
      this.type = type;
      this.proof = proof;
    }
  }

  private static RType makeRType(CoreBinding binding, CoreExpression paramType) {
    CoreFunCallExpression equality = paramType.toEquality();
    return equality != null ? new EqType(binding, equality, equality.getDefCallArguments().get(1), equality.getDefCallArguments().get(2)) : new RType(binding, paramType);
  }

  private static class NegationData {
    final List<RType> types;
    final Deque<Object> instructions; // either CoreConstructor or not; the latter indicates a variable

    NegationData(List<RType> types, Deque<Object> instructions) {
      this.types = types;
      this.instructions = instructions;
    }

    private ConcreteExpression makeExpression(Deque<ConcreteExpression> arguments, CoreConstructor constructor, ConcreteFactory factory) {
      List<ConcreteArgument> args = new ArrayList<>();
      CoreParameter param = constructor.getParameters();
      if (param.hasNext() && !param.isExplicit()) {
        for (CoreParameter dataParam = constructor.getDataType().getParameters(); dataParam.hasNext(); dataParam = dataParam.getNext()) {
          args.add(factory.arg(factory.hole(), false));
        }
      }
      for (; param.hasNext(); param = param.getNext()) {
        Object con = instructions.removeFirst();
        if (con instanceof CoreConstructor) {
          args.add(factory.arg(makeExpression(arguments, (CoreConstructor) con, factory), param.isExplicit()));
        } else {
          args.add(factory.arg(arguments.removeFirst(), param.isExplicit()));
        }
      }
      return factory.app(factory.ref(constructor.getRef()), args);
    }

    Negation make(List<CoreParameter> parameters, CoreExpression codomain, ConcreteExpression proof, ConcreteFactory factory) {
      return new Negation(types, codomain, arguments -> {
        List<ConcreteArgument> args = new ArrayList<>();
        for (CoreParameter param : parameters) {
          Object con = instructions.removeFirst();
          if (con instanceof CoreConstructor) {
            args.add(factory.arg(makeExpression(arguments, (CoreConstructor) con, factory), param.isExplicit()));
          } else {
            args.add(factory.arg(arguments.removeFirst(), param.isExplicit()));
          }
        }
        return factory.app(proof, args);
      });
    }
  }

  private boolean isAppropriateDataCall(CoreExpression type) {
    if (!(type instanceof CoreDataCallExpression)) {
      return false;
    }
    CoreDataDefinition dataDef = ((CoreDataCallExpression) type).getDefinition();
    return dataDef != ext.prelude.getPath() && dataDef != ext.prelude.getInterval() && dataDef.getRecursiveDefinitions().isEmpty();
  }

  private void makeNegationData(Deque<CoreParameter> parameters, CoreExpression codomain, NegationData negationData, List<NegationData> result) {
    while (!parameters.isEmpty()) {
      CoreParameter parameter = parameters.removeFirst();
      CoreExpression type = parameter.getTypeExpr().normalize(NormalizationMode.WHNF);
      List<CoreDataCallExpression.ConstructorWithParameters> constructors = isAppropriateDataCall(type) ? ((CoreDataCallExpression) type).computeMatchedConstructorsWithParameters() : null;
      if (constructors != null) {
        boolean ok = codomain == null || !codomain.findFreeBinding(parameter.getBinding());
        if (ok) {
          for (CoreParameter param : parameters) {
            if (param.getTypeExpr().findFreeBinding(parameter.getBinding())) {
              ok = false;
              break;
            }
          }
        }
        if (ok) {
          for (CoreDataCallExpression.ConstructorWithParameters constructor : constructors) {
            NegationData conData = new NegationData(new ArrayList<>(negationData.types), new ArrayDeque<>(negationData.instructions));
            conData.instructions.addLast(constructor.constructor);
            List<CoreParameter> conParams = new ArrayList<>();
            for (CoreParameter conParam = constructor.parameters; conParam.hasNext(); conParam = conParam.getNext()) {
              conParams.add(conParam);
            }
            for (int i = conParams.size() - 1; i >= 0; i--) {
              parameters.addFirst(conParams.get(i));
            }
            makeNegationData(parameters, null, conData, result);
          }
          return;
        }
      }

      negationData.types.add(makeRType(parameter.getBinding(), type));
      negationData.instructions.addLast(Boolean.TRUE); // it doesn't matter what we add here
    }
    result.add(negationData);
  }

  private static class TransData {
    final CoreAppExpression leftApp;
    final int rightArg;
    final ConcreteExpression proof;

    private TransData(CoreAppExpression leftApp, int rightArg, ConcreteExpression proof) {
      this.leftApp = leftApp;
      this.rightArg = rightArg;
      this.proof = proof;
    }
  }

  private boolean makeNegation(CoreExpression type, ConcreteExpression proof, ConcreteFactory factory, List<Negation> negations, Values<UncheckedExpression> values, Map<CoreClassField, Map<Integer, List<TransData>>> transGraphs) {
    List<CoreParameter> parameters;
    if (type instanceof CorePiExpression) {
      parameters = new ArrayList<>();
      type = type.getPiParameters(parameters).normalize(NormalizationMode.WHNF);
    } else {
      parameters = Collections.emptyList();
    }

    if (isEmpty(type)) {
      List<NegationData> negationDataList = new ArrayList<>();
      makeNegationData(new ArrayDeque<>(parameters), type, new NegationData(new ArrayList<>(), new ArrayDeque<>()), negationDataList);
      for (NegationData negationData : negationDataList) {
        negations.add(negationData.make(parameters, type, proof, factory));
      }
      return true;
    } else if (type instanceof CoreAppExpression) {
      CoreAppExpression app2 = (CoreAppExpression) type;
      if (app2.getFunction() instanceof CoreAppExpression) {
        CoreAppExpression app1 = (CoreAppExpression) app2.getFunction();
        CoreExpression fun = app1.getFunction().normalize(NormalizationMode.WHNF);
        if (fun instanceof CoreFieldCallExpression) {
          CoreClassField field = ((CoreFieldCallExpression) fun).getDefinition();
          FieldKey.Data irreflexivityData = field.getUserData(ext.irreflexivityKey);
          if (irreflexivityData != null) {
            if (field.getUserData(ext.transitivityKey) != null) {
              transGraphs.computeIfAbsent(field, f -> new HashMap<>()).computeIfAbsent(values.addValue(app1.getArgument()), i -> new ArrayList<>()).add(new TransData(app1, values.addValue(app2.getArgument()), proof));
              return true;
            }

            List<CoreParameter> irrParams = new ArrayList<>(2);
            CoreExpression irrCodomain = irreflexivityData.field.getResultType().getPiParameters(irrParams);
            if (irrParams.size() != 2) { // This shouldn't happen
              return false;
            }
            negations.add(new Negation(Collections.singletonList(new EqType(null, null, app1.getArgument(), app2.getArgument())), irrCodomain, args -> {
              List<ConcreteArgument> irrArgs = new ArrayList<>(2);
              if (irrParams.get(0).isExplicit()) {
                irrArgs.add(factory.arg(factory.hole(), true));
              }
              irrArgs.add(factory.arg(factory.app(factory.ref(ext.transportInv.getRef()), true, Arrays.asList(factory.core(app1.computeTyped()), args.getFirst(), proof)), irrParams.get(1).isExplicit()));
              return factory.app(factory.ref(irreflexivityData.field.getRef()), irrArgs);
            }));
            return true;
          }
        }
      }
    }

    return false;
  }

  public TypedExpression checkCore(ConcreteExpression argument, CoreExpression expectedType, boolean withExpectedType, ConcreteSourceNode marker, ExpressionTypechecker typechecker) {
    ConcreteExpression expr = check(Context.TRIVIAL, argument, expectedType, withExpectedType, marker, typechecker);
    if (expr instanceof ConcreteLamExpression || expr instanceof ConcreteCaseExpression && !((ConcreteCaseExpression) expr).getClauses().isEmpty()) {
      return Utils.tryTypecheck(typechecker, tc -> tc.typecheck(expr, expectedType));
    }
    return expr == null ? null : typechecker.typecheck(expr, expectedType);
  }

  public ConcreteExpression check(ConcreteExpression argument, CoreExpression expectedType, boolean withExpectedType, ConcreteSourceNode marker, ExpressionTypechecker typechecker) {
    return check(Context.TRIVIAL, argument, expectedType, withExpectedType, marker, typechecker);
  }

  public ConcreteExpression check(Context context, ConcreteExpression argument, CoreExpression expectedType, boolean withExpectedType, ConcreteSourceNode marker, ExpressionTypechecker typechecker) {
    CoreExpression type;
    List<CoreParameter> parameters;
    if (expectedType != null) {
      parameters = new ArrayList<>();
      type = expectedType.getPiParameters(parameters);
    } else {
      parameters = Collections.emptyList();
      type = null;
    }

    if (parameters.isEmpty()) {
      return checkInternal(context, argument, type, withExpectedType, marker, typechecker);
    }

    ConcreteFactory factory = ext.factory.withData(marker.getData());
    List<ConcreteParameter> cParams = new ArrayList<>();
    for (CoreParameter parameter : parameters) {
      cParams.add(factory.param(parameter.isExplicit(), factory.local(ext.renamerFactory.getNameFromBinding(parameter.getBinding(), null))));
    }

    return factory.lam(cParams, factory.meta("contradiction_lambda", new MetaDefinition() {
      @Override
      public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        return checkCore(argument, type, withExpectedType, marker, typechecker);
      }
    }));
  }

  private ConcreteExpression checkInternal(Context context, ConcreteExpression argument, CoreExpression expectedType, boolean withExpectedType, ConcreteSourceNode marker, ExpressionTypechecker typechecker) {
    ContextHelper contextHelper = new ContextHelper(context, argument);
    ConcreteFactory factory = ext.factory.withData(marker.getData());

    CoreExpression type = null;
    ConcreteExpression contr = null;
    Values<UncheckedExpression> values = new Values<>(typechecker, marker);
    Map<CoreClassField, Map<Integer, List<TransData>>> transGraphs = new HashMap<>();
    List<Negation> negations = new ArrayList<>();
    List<ConcreteClause> clauses = new ArrayList<>();
    if (argument != null && contextHelper.meta == null) {
      TypedExpression contradiction = typechecker.typecheck(argument, null);
      if (contradiction == null) {
        return null;
      }
      type = contradiction.getType().normalize(NormalizationMode.WHNF);
      if (isEmpty(type)) {
        contr = factory.core(contradiction);
      } else {
        if (!makeNegation(type, factory.core(contradiction), factory, negations, values, transGraphs)) {
          typechecker.getErrorReporter().report(new TypeError("The expression does not prove a contradiction", type, argument));
          return null;
        }
      }
    }

    if (contr == null) {
      BunchedEquivalenceClosure<Integer> equivalenceClosure = new BunchedEquivalenceClosure<>(factory.ref(ext.prelude.getIdp().getRef()), factory.ref(ext.inv.getRef()), factory.ref(ext.concat.getRef()), factory);
      ValuesRelationClosure closure = new ValuesRelationClosure(values, equivalenceClosure);
      Values<CoreExpression> typeValues = new Values<>(typechecker, marker);
      Map<Integer, RType> assumptions = new HashMap<>();
      boolean searchForContradiction = negations.isEmpty() && transGraphs.isEmpty();
      List<Integer> conIndices = new ArrayList<>();
      for (CoreBinding binding : contextHelper.getAllBindings(typechecker)) {
        type = binding.getTypeExpr().normalize(NormalizationMode.WHNF);
        List<CoreDataCallExpression.ConstructorWithParameters> constructors = isAppropriateDataCall(type) ? ((CoreDataCallExpression) type).computeMatchedConstructorsWithParameters() : null;
        if (constructors != null && constructors.isEmpty()) {
          contr = factory.ref(binding);
          break;
        }

        if (constructors != null) {
          contr = factory.ref(binding);
          for (CoreDataCallExpression.ConstructorWithParameters con : constructors) {
            List<ConcretePattern> subPatterns = new ArrayList<>();
            for (CoreParameter param = con.parameters; param.hasNext(); param = param.getNext()) {
              subPatterns.add(factory.refPattern(factory.local(ext.renamerFactory.getNameFromBinding(param.getBinding(), null) + "1"), null));
            }
            clauses.add(factory.clause(Collections.singletonList(factory.conPattern(con.constructor.getRef(), subPatterns)), factory.meta("case_" + con.constructor.getName(), new MetaDefinition() {
              @Override
              public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
                ConcreteExpression result = check(HidingContext.make(context, Collections.singleton(binding)), null, null, true, marker, typechecker);
                return result == null ? null : typechecker.typecheck(result, contextData.getExpectedType());
              }
            })));
          }
          break;
        }

        RType rType = makeRType(binding, type);
        RType prev = null;
        if (rType instanceof EqType) {
          CoreExpression expr1 = ((EqType) rType).leftExpr.normalize(NormalizationMode.WHNF);
          CoreExpression expr2 = ((EqType) rType).rightExpr.normalize(NormalizationMode.WHNF);
          int value1 = values.addValue(expr1);
          int value2 = values.addValue(expr2);
          if (expr1 instanceof CoreConCallExpression || expr1 instanceof CoreIntegerExpression) {
            conIndices.add(value1);
          }
          if (expr2 instanceof CoreConCallExpression || expr2 instanceof CoreIntegerExpression) {
            conIndices.add(value2);
          }
          closure.addRelation(value1, value2, factory.ref(binding));
        } else {
          prev = assumptions.putIfAbsent(typeValues.addValue(type), rType);
        }
        if (searchForContradiction && prev == null) {
          makeNegation(type, factory.ref(binding), factory, negations, values, transGraphs);
        }
      }

      if (contr == null) {
        loop:
        for (Integer conIndex1 : conIndices) {
          for (Integer conIndex2 : conIndices) {
            if (equivalenceClosure.areRelated(conIndex1, conIndex2) && values.getValue(conIndex1).areDisjointConstructors(values.getValue(conIndex2))) {
              contr = equivalenceClosure.checkRelation(conIndex1, conIndex2);
              type = null;
              break loop;
            }
          }
        }

        if (contr == null) {
          loop:
          for (Negation negation : negations) {
            Deque<ConcreteExpression> arguments = new ArrayDeque<>();
            Map<CoreBinding, CoreExpression> subst = new HashMap<>();
            for (int i = 0; i < negation.assumptions.size(); i++) {
              RType assumption = negation.assumptions.get(i);
              boolean isFree = false;
              for (int j = i + 1; j < negation.assumptions.size(); j++) {
                if (negation.assumptions.get(j).type.findFreeBinding(assumption.binding)) {
                  isFree = true;
                  break;
                }
              }

              ConcreteExpression argExpr;
              if (isFree) {
                UncheckedExpression paramType = assumption.type.findFreeBindings(subst.keySet()) != null ? assumption.type.substitute(subst) : assumption.type;
                CoreExpression checkedType;
                if (paramType instanceof CoreExpression) {
                  checkedType = (CoreExpression) paramType;
                } else {
                  TypedExpression typedExpr = typechecker.check(paramType, marker);
                  if (typedExpr == null) {
                    continue loop;
                  }
                  checkedType = typedExpr.getExpression();
                }
                argExpr = factory.hole();
                subst.put(assumption.binding, Objects.requireNonNull(typechecker.typecheck(argExpr, checkedType)).getExpression());
              } else {
                if (assumption instanceof EqType) {
                  argExpr = closure.checkRelation(((EqType) assumption).leftExpr.substitute(subst), ((EqType) assumption).rightExpr.substitute(subst));
                  if (argExpr == null) {
                    continue loop;
                  }
                } else {
                  int index = typeValues.getIndex(assumption.type.substitute(subst));
                  if (index == -1) {
                    continue loop;
                  }
                  argExpr = factory.ref(assumptions.get(index).binding);
                }
              }

              arguments.add(argExpr);
            }

            contr = negation.proof.apply(arguments);
            type = negation.type;
            break;
          }

          if (contr == null) {
            loop:
            for (Map.Entry<CoreClassField, Map<Integer, List<TransData>>> entry : transGraphs.entrySet()) {
              for (Integer index : entry.getValue().keySet()) {
                Set<Integer> visited = new HashSet<>();
                List<TransData> transDataList = new ArrayList<>();
                Object eqProof = findContradiction(equivalenceClosure, entry.getValue(), index, index, visited, transDataList);
                if (eqProof != null) {
                  ConcreteExpression transProof = transDataList.get(0).proof;
                  FieldKey.Data transitivityData = Objects.requireNonNull(entry.getKey().getUserData(ext.transitivityKey));
                  for (int i = 1; i < transDataList.size(); i++) {
                    List<ConcreteArgument> args = new ArrayList<>(5);
                    for (int j = 0; j < 3; j++) {
                      if (transitivityData.parametersExplicitness.get(j)) {
                        args.add(factory.arg(factory.hole(), true));
                      }
                    }
                    args.add(factory.arg(transDataList.get(i).proof, transitivityData.parametersExplicitness.get(3)));
                    args.add(factory.arg(transProof, transitivityData.parametersExplicitness.get(4)));
                    transProof = factory.app(factory.ref(transitivityData.field.getRef()), args);
                  }

                  if (eqProof instanceof ConcreteExpression) {
                    transProof = factory.app(factory.ref(ext.transportInv.getRef()), true, Arrays.asList(factory.core(transDataList.get(transDataList.size() - 1).leftApp.computeTyped()), (ConcreteExpression) eqProof, transProof));
                  }

                  List<CoreParameter> irrParams = new ArrayList<>(2);
                  FieldKey.Data irreflexivityData = Objects.requireNonNull(entry.getKey().getUserData(ext.irreflexivityKey));
                  type = irreflexivityData.field.getResultType().getPiParameters(irrParams);
                  List<ConcreteArgument> irrArgs = new ArrayList<>(2);
                  if (irrParams.get(0).isExplicit()) {
                    irrArgs.add(factory.arg(factory.hole(), true));
                  }
                  irrArgs.add(factory.arg(transProof, irrParams.get(1).isExplicit()));
                  contr = factory.app(factory.ref(irreflexivityData.field.getRef()), irrArgs);
                  break loop;
                }
              }
            }
          }

          if (contr == null) {
            typechecker.getErrorReporter().report(new TypecheckingError("Cannot infer contradiction", marker));
            return null;
          }
        }
      }
    }

    return expectedType != null && type != null && expectedType.compare(type, CMP.EQ) ? contr : factory.caseExpr(false, Collections.singletonList(factory.caseArg(contr, null, null)), withExpectedType ? null : factory.ref(ext.Empty.getRef()), null, clauses);
  }

  private Object findContradiction(BinaryRelationClosure<Integer> closure, Map<Integer, List<TransData>> map, int index, int startIndex, Set<Integer> visited, List<TransData> result) {
    if (!visited.add(index)) {
      return null;
    }

    List<TransData> transDataList = map.get(index);
    if (transDataList == null) {
      return null;
    }

    for (TransData transData : transDataList) {
      if (startIndex == transData.rightArg) {
        result.add(transData);
        return true;
      }
      Object resultExpr = closure.checkRelation(startIndex, transData.rightArg);
      if (resultExpr != null) {
        result.add(transData);
        return resultExpr;
      }

      resultExpr = findContradiction(closure, map, transData.rightArg, startIndex, visited, result);
      if (resultExpr != null) {
        result.add(transData);
        return resultExpr;
      }
    }

    return null;
  }

  public static boolean isEmpty(CoreExpression type) {
    if (type instanceof CoreDataCallExpression) {
      List<CoreConstructor> constructors = ((CoreDataCallExpression) type).computeMatchedConstructors();
      return constructors != null && constructors.isEmpty();
    }
    return false;
  }
}
