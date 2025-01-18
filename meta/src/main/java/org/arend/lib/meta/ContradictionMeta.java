package org.arend.lib.meta;

import org.arend.ext.concrete.*;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteCaseExpression;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteLamExpression;
import org.arend.ext.concrete.pattern.ConcretePattern;
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
  public boolean @Nullable [] argumentExplicitness() {
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

  private record Negation(List<RType> assumptions, CoreExpression type, Function<Deque<ConcreteExpression>, ConcreteExpression> proof) {}

  private static RType makeRType(CoreBinding binding, CoreExpression paramType) {
    CoreFunCallExpression equality = paramType.toEquality();
    return equality != null ? new EqType(binding, equality, equality.getDefCallArguments().get(1), equality.getDefCallArguments().get(2)) : new RType(binding, paramType);
  }

  /**
   * @param instructions either CoreConstructor or not; the latter indicates a variable
   */
  private record NegationData(List<RType> types, Deque<Object> instructions) {
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
      CoreExpression type = Utils.unfoldType(parameter.getTypeExpr().normalize(NormalizationMode.WHNF));
      List<CoreDataCallExpression.ConstructorWithDataArguments> constructors = isAppropriateDataCall(type) ? type.computeMatchedConstructorsWithDataArguments() : null;
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
          for (CoreDataCallExpression.ConstructorWithDataArguments constructor : constructors) {
            NegationData conData = new NegationData(new ArrayList<>(negationData.types), new ArrayDeque<>(negationData.instructions));
            conData.instructions.addLast(constructor.getConstructor());
            List<CoreParameter> conParams = new ArrayList<>();
            for (CoreParameter conParam = constructor.getParameters(); conParam.hasNext(); conParam = conParam.getNext()) {
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

  private record Triple(CoreFieldCallExpression fun, CoreExpression arg1, CoreExpression arg2) {

    public static Triple make(CoreExpression expr) {
        if (!(expr instanceof CoreAppExpression app2)) {
          return null;
        }

        if (!(app2.getFunction() instanceof CoreAppExpression app1)) {
          return null;
        }

        CoreExpression fun = app1.getFunction();
        return fun instanceof CoreFieldCallExpression ? new Triple((CoreFieldCallExpression) fun, app1.getArgument(), app2.getArgument()) : null;
      }
    }

  private boolean makeNegation(CoreExpression type, ConcreteExpression proof, ConcreteFactory factory, List<Negation> negations, Values<UncheckedExpression> values, Map<CoreClassField, Map<Integer, List<Edge<Integer>>>> transGraphs) {
    List<CoreParameter> parameters;
    if (type instanceof CorePiExpression) {
      parameters = new ArrayList<>();
      type = type.getPiParameters(parameters);
    } else {
      parameters = Collections.emptyList();
    }

    if (isEmpty(type)) {
      if (parameters.size() == 1) {
        Triple triple = Triple.make(Utils.unfoldType(parameters.get(0).getTypeExpr().normalize(NormalizationMode.WHNF)));
        if (triple != null) {
          if (triple.fun.getDefinition() == ext.equationMeta.less) {
            CoreExpression argType = triple.fun.getArgument().computeType().normalize(NormalizationMode.WHNF);
            if (argType instanceof CoreClassCallExpression && ((CoreClassCallExpression) argType).getDefinition().isSubClassOf(ext.equationMeta.LinearOrder)) {
              Integer index1 = values.addValue(triple.arg2);
              transGraphs.computeIfAbsent(ext.equationMeta.less, k -> new HashMap<>()).computeIfAbsent(index1, k -> new ArrayList<>())
                .add(new Edge<>(index1, values.addValue(triple.arg1), proof, EdgeKind.LESS_OR_EQ, null));
            }
          }
        }
      }

      List<NegationData> negationDataList = new ArrayList<>();
      makeNegationData(new ArrayDeque<>(parameters), type, new NegationData(new ArrayList<>(), new ArrayDeque<>()), negationDataList);
      for (NegationData negationData : negationDataList) {
        negations.add(negationData.make(parameters, type, proof, factory));
      }
      return true;
    } else if (parameters.isEmpty() && type instanceof CoreAppExpression app2) {
      if (app2.getFunction() instanceof CoreAppExpression app1) {
        CoreExpression fun = app1.getFunction();
        if (fun instanceof CoreFieldCallExpression) {
          CoreClassField field = ((CoreFieldCallExpression) fun).getDefinition();
          if (field.getUserData(ext.transitivityKey) != null) {
            Integer index1 = values.addValue(app1.getArgument());
            transGraphs.computeIfAbsent(field, f -> new HashMap<>()).computeIfAbsent(index1, i -> new ArrayList<>()).add(new Edge<>(index1, values.addValue(app2.getArgument()), proof, EdgeKind.LESS, factory.core(app1.computeTyped())));
            return true;
          }
          FieldKey.Data irreflexivityData = field.getUserData(ext.irreflexivityKey);
          if (irreflexivityData != null) {
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
        return checkCore(argument, contextData.getExpectedType(), withExpectedType, marker, typechecker);
      }
    }));
  }

  private enum EdgeKind { EQ, EQ_INV, LESS, LESS_OR_EQ }

  private record Edge<V>(V source, V target, ConcreteExpression proof, EdgeKind kind, ConcreteExpression leftApp) {}

  /**
   * Finds the shortest path from {@code first} to {@code last} that contains a LESS edge.
   */
  private <V> List<Edge<V>> bfs(Map<V, List<Edge<V>>> graph, V first, V last) {
    Map<V, Boolean> visited = new HashMap<>(); // true means we met a LESS edge on the way to the vertex
    Map<V, Edge<V>> parent = new HashMap<>();
    visited.put(first, false);
    Deque<V> queue = new ArrayDeque<>();
    queue.addLast(first);
    while (!queue.isEmpty()) {
      V vertex = queue.removeFirst();
      boolean metLess = Boolean.TRUE.equals(visited.get(vertex));
      if (metLess && vertex.equals(last)) {
        List<Edge<V>> result = new ArrayList<>();
        metLess = false;
        while (!(metLess && vertex.equals(first))) {
          Edge<V> edge = parent.get(vertex);
          vertex = edge.source;
          result.add(edge);
          if (!metLess && edge.kind == EdgeKind.LESS) metLess = true;
        }
        Collections.reverse(result);
        return result;
      }

      List<Edge<V>> edges = graph.get(vertex);
      if (edges == null) continue;
      for (Edge<V> edge : edges) {
        Boolean targetVisited = visited.get(edge.target);
        if (targetVisited == null || !targetVisited && (metLess || edge.kind == EdgeKind.LESS)) {
          visited.put(edge.target, metLess || edge.kind == EdgeKind.LESS);
          queue.add(edge.target);
          parent.put(edge.target, edge);
        }
      }
    }
    return null;
  }

  private ConcreteExpression makeTransitivityProof(CoreClassField field, List<Edge<Integer>> path, ConcreteFactory factory) {
    FieldKey.Data transitivityData = Objects.requireNonNull(field.getUserData(ext.transitivityKey));
    int i0 = 0;
    while (path.get(i0).kind != EdgeKind.LESS) {
      i0++;
    }
    ConcreteExpression transProof = path.get(i0).proof;
    for (int i = (i0 + 1) % path.size(); i != i0; i = (i + 1) % path.size()) {
      if (path.get(i).kind == EdgeKind.LESS) {
        List<ConcreteArgument> args = new ArrayList<>(5);
        for (int j = 0; j < 3; j++) {
          if (transitivityData.parametersExplicitness.get(j)) {
            args.add(factory.arg(factory.hole(), true));
          }
        }
        args.add(factory.arg(transProof, transitivityData.parametersExplicitness.get(3)));
        args.add(factory.arg(path.get(i).proof, transitivityData.parametersExplicitness.get(4)));
        transProof = factory.app(factory.ref(transitivityData.field.getRef()), args);
      } else if (path.get(i).kind == EdgeKind.LESS_OR_EQ) {
        transProof = factory.app(factory.ref(ext.equationMeta.lessTransitiveLeft.getRef()), true, Arrays.asList(transProof, path.get(i).proof));
      } else {
        transProof = factory.app(factory.ref((path.get(i).kind == EdgeKind.EQ ? ext.transport : ext.transportInv).getRef()), true, Arrays.asList(path.get(i0).leftApp, path.get(i).proof, transProof));
      }
    }
    return transProof;
  }

  private ConcreteExpression checkInternal(Context context, ConcreteExpression argument, CoreExpression expectedType, boolean withExpectedType, ConcreteSourceNode marker, ExpressionTypechecker typechecker) {
    ContextHelper contextHelper = new ContextHelper(context, argument);
    ConcreteFactory factory = ext.factory.withData(marker.getData());

    CoreExpression type = null;
    ConcreteExpression contr = null;
    Values<UncheckedExpression> values = new Values<>(typechecker, marker);
    Map<CoreClassField, Map<Integer, List<Edge<Integer>>>> transGraphs = new HashMap<>();
    List<Negation> negations = new ArrayList<>();
    List<ConcreteClause> clauses = new ArrayList<>();
    if (argument != null && contextHelper.meta == null) {
      TypedExpression contradiction = typechecker.typecheck(argument, null);
      if (contradiction == null) {
        return null;
      }
      type = Utils.unfoldType(contradiction.getType().normalize(NormalizationMode.WHNF));
      if (isEmpty(type)) {
        contr = factory.core(contradiction);
      } else {
        if (!makeNegation(type, factory.core(contradiction), factory, negations, values, transGraphs)) {
          typechecker.getErrorReporter().report(new TypeError(typechecker.getExpressionPrettifier(), "The expression does not prove a contradiction", type, argument));
          return null;
        }
      }
    }

    if (contr == null) {
      BunchedEquivalenceClosure<Integer> equivalenceClosure = new BunchedEquivalenceClosure<>(factory.ref(ext.prelude.getIdpRef()), factory.ref(ext.inv.getRef()), factory.ref(ext.concat.getRef()), factory);
      ValuesRelationClosure closure = new ValuesRelationClosure(values, equivalenceClosure);
      List<Edge<Integer>> equalities = new ArrayList<>();
      Values<CoreExpression> typeValues = new Values<>(typechecker, marker);
      Map<Integer, RType> assumptions = new HashMap<>();
      boolean searchForContradiction = negations.isEmpty() && transGraphs.isEmpty();
      List<Integer> conIndices = new ArrayList<>();
      for (CoreBinding binding : contextHelper.getAllBindings(typechecker)) {
        type = Utils.unfoldType(binding.getTypeExpr().normalize(NormalizationMode.WHNF));
        List<CoreDataCallExpression.ConstructorWithDataArguments> constructors = isAppropriateDataCall(type) ? type.computeMatchedConstructorsWithDataArguments() : null;
        if (constructors != null && constructors.isEmpty()) {
          contr = factory.ref(binding);
          break;
        }

        if (constructors != null) {
          contr = factory.ref(binding);
          for (CoreDataCallExpression.ConstructorWithDataArguments con : constructors) {
            List<ConcretePattern> subPatterns = new ArrayList<>();
            for (CoreParameter param = con.getParameters(); param.hasNext(); param = param.getNext()) {
              subPatterns.add(factory.refPattern(factory.local(ext.renamerFactory.getNameFromBinding(param.getBinding(), null) + "1"), null));
            }
            clauses.add(factory.clause(Collections.singletonList(factory.conPattern(con.getConstructor().getRef(), subPatterns)), factory.meta("case_" + con.getConstructor().getName(), new MetaDefinition() {
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
          ConcreteExpression proof = factory.ref(binding);
          closure.addRelation(value1, value2, proof);
          equalities.add(new Edge<>(value1, value2, proof, EdgeKind.EQ, null));
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
            for (Map.Entry<CoreClassField, Map<Integer, List<Edge<Integer>>>> entry : transGraphs.entrySet()) {
              for (Edge<Integer> edge : equalities) {
                entry.getValue().computeIfAbsent(edge.source, k -> new ArrayList<>()).add(edge);
                entry.getValue().computeIfAbsent(edge.target, k -> new ArrayList<>()).add(new Edge<>(edge.target, edge.source, edge.proof, EdgeKind.EQ_INV, null));
              }

              for (Negation negation : negations) {
                List<Triple> triples = new ArrayList<>(negation.assumptions.size());
                for (RType assumption : negation.assumptions) {
                  Triple triple = Triple.make(assumption.type);
                  if (triple == null || triple.fun.getDefinition() != entry.getKey()) break;
                  if (negation.assumptions.size() == 1) {
                    CoreExpression instanceType = triple.fun.getArgument().computeType().normalize(NormalizationMode.WHNF);
                    if (instanceType instanceof CoreClassCallExpression && ((CoreClassCallExpression) instanceType).getDefinition().isSubClassOf(ext.equationMeta.LinearOrder)) break;
                  }
                  triples.add(triple);
                }
                if (triples.size() != negation.assumptions.size()) continue;

                Deque<ConcreteExpression> negationArgs = new ArrayDeque<>(triples.size());
                for (Triple triple : triples) {
                  List<Edge<Integer>> path = bfs(entry.getValue(), values.addValue(triple.arg1), values.addValue(triple.arg2));
                  if (path == null) break;
                  negationArgs.add(makeTransitivityProof(entry.getKey(), path, factory));
                }

                if (negationArgs.size() == triples.size()) {
                  contr = negation.proof.apply(negationArgs);
                  type = negation.type;
                  break loop;
                }
              }

              FieldKey.Data irreflexivityData = entry.getKey().getUserData(ext.irreflexivityKey);
              if (irreflexivityData == null) continue;

              for (Integer vertex : entry.getValue().keySet()) {
                List<Edge<Integer>> path = bfs(entry.getValue(), vertex, vertex);
                if (path != null) {
                  ConcreteExpression transProof = makeTransitivityProof(entry.getKey(), path, factory);
                  List<CoreParameter> irrParams = new ArrayList<>(2);
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

  public static boolean isEmpty(CoreExpression type) {
    if (type instanceof CoreDataCallExpression) {
      List<CoreConstructor> constructors = ((CoreDataCallExpression) type).computeMatchedConstructors();
      return constructors != null && constructors.isEmpty();
    }
    return false;
  }
}
