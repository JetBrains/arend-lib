package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcretePattern;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteCaseExpression;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.context.Context;
import org.arend.lib.context.HidingContext;
import org.arend.lib.error.TypeError;
import org.arend.lib.meta.closure.EqualityClosure;
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
    ConcreteExpression expr = check(contextData.getArguments().isEmpty() ? null : contextData.getArguments().get(0).getExpression(), contextData.getExpectedType(), contextData.getExpectedType() != null, contextData.getReferenceExpression(), typechecker);
    if (expr instanceof ConcreteCaseExpression && !((ConcreteCaseExpression) expr).getClauses().isEmpty()) {
      return Utils.tryTypecheck(typechecker, tc -> tc.typecheck(expr, contextData.getExpectedType()));
    }
    return expr == null ? null : typechecker.typecheck(expr, contextData.getExpectedType());
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
    final Function<List<ConcreteExpression>, ConcreteExpression> proof;

    private Negation(List<RType> assumptions, CoreExpression type, Function<List<ConcreteExpression>, ConcreteExpression> proof) {
      this.assumptions = assumptions;
      this.type = type;
      this.proof = proof;
    }
  }

  private static RType makeRType(CoreBinding binding, CoreExpression paramType) {
    CoreFunCallExpression equality = paramType.toEquality();
    return equality != null ? new EqType(binding, equality, equality.getDefCallArguments().get(1), equality.getDefCallArguments().get(2)) : new RType(binding, paramType);
  }

  public boolean makeNegation(CoreExpression type, ConcreteExpression proof, ConcreteFactory factory, List<Negation> negations) {
    List<CoreParameter> parameters;
    if (type instanceof CorePiExpression) {
      parameters = new ArrayList<>();
      type = type.getPiParameters(parameters).normalize(NormalizationMode.WHNF);
    } else {
      parameters = Collections.emptyList();
    }

    if (isEmpty(type)) {
      List<RType> types = new ArrayList<>(parameters.size());
      for (CoreParameter parameter : parameters) {
        types.add(makeRType(parameter.getBinding(), parameter.getTypeExpr().normalize(NormalizationMode.WHNF)));
      }
      negations.add(new Negation(types, type, arguments -> {
        List<ConcreteArgument> args = new ArrayList<>(arguments.size());
        for (int i = 0; i < arguments.size(); i++) {
          args.add(factory.arg(arguments.get(i), parameters.get(i).isExplicit()));
        }
        return factory.app(proof, args);
      }));
      return true;
    } else if (type instanceof CoreAppExpression) {
      CoreAppExpression app2 = (CoreAppExpression) type;
      if (app2.getFunction() instanceof CoreAppExpression) {
        CoreAppExpression app1 = (CoreAppExpression) app2.getFunction();
        CoreExpression fun = app1.getFunction().normalize(NormalizationMode.WHNF);
        if (fun instanceof CoreFieldCallExpression) {
          CoreClassField irreflexivity = ((CoreFieldCallExpression) fun).getDefinition().getUserData(ext.irreflexivityKey);
          if (irreflexivity != null) {
            List<CoreParameter> irrParams = new ArrayList<>(2);
            CoreExpression irrCodomain = irreflexivity.getResultType().getPiParameters(irrParams);
            if (irrParams.size() != 2) { // This shouldn't happen
              return false;
            }
            negations.add(new Negation(Collections.singletonList(new EqType(null, null, app1.getArgument(), app2.getArgument())), irrCodomain, args -> {
              List<ConcreteArgument> irrArgs = new ArrayList<>(2);
              if (irrParams.get(0).isExplicit()) {
                irrArgs.add(factory.arg(factory.hole(), true));
              }
              irrArgs.add(factory.arg(factory.app(factory.ref(ext.transportInv.getRef()), true, Arrays.asList(factory.core(app1.computeTyped()), args.get(0), proof)), irrParams.get(1).isExplicit()));
              return factory.app(factory.ref(irreflexivity.getRef()), irrArgs);
            }));
            return true;
          }
        }
      }
    }

    return false;
  }

  public ConcreteExpression check(ConcreteExpression argument, CoreExpression expectedType, boolean withExpectedType, ConcreteSourceNode marker, ExpressionTypechecker typechecker) {
    return check(Context.TRIVIAL, argument, expectedType, withExpectedType, marker, typechecker);
  }

  public ConcreteExpression check(Context context, ConcreteExpression argument, CoreExpression expectedType, boolean withExpectedType, ConcreteSourceNode marker, ExpressionTypechecker typechecker) {
    ContextHelper contextHelper = new ContextHelper(context, argument);
    ConcreteFactory factory = ext.factory.withData(marker.getData());

    CoreExpression type = null;
    ConcreteExpression contr = null;
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
        if (!makeNegation(type, factory.core(contradiction), factory, negations)) {
          typechecker.getErrorReporter().report(new TypeError("The expression does not prove a contradiction", type, argument));
          return null;
        }
      }
    }

    if (contr == null) {
      ValuesRelationClosure closure = new ValuesRelationClosure(new Values<>(typechecker, marker), new EqualityClosure<>(ext, factory));
      Values<CoreExpression> typeValues = new Values<>(typechecker, marker);
      Map<Integer, RType> assumptions = new HashMap<>();
      boolean searchForContradiction = negations.isEmpty();
      for (CoreBinding binding : contextHelper.getAllBindings(typechecker)) {
        type = binding.getTypeExpr().normalize(NormalizationMode.WHNF);
        List<CoreDataCallExpression.ConstructorWithParameters> constructors = type instanceof CoreDataCallExpression ? ((CoreDataCallExpression) type).computeMatchedConstructorsWithParameters() : null;
        if (constructors != null && constructors.isEmpty()) {
          contr = factory.ref(binding);
          break;
        }

        if (constructors != null && ((CoreDataCallExpression) type).getDefinition() != ext.prelude.getPath() && ((CoreDataCallExpression) type).getDefinition().getRecursiveDefinitions().isEmpty()) {
          contr = factory.ref(binding);
          for (CoreDataCallExpression.ConstructorWithParameters con : constructors) {
            List<ConcretePattern> subPatterns = new ArrayList<>();
            for (CoreParameter param = con.parameters; param.hasNext(); param = param.getNext()) {
              subPatterns.add(factory.refPattern(factory.local(ext.renamerFactory.getNameFromType(param.getTypeExpr(), null) + "1"), null));
            }
            clauses.add(factory.clause(Collections.singletonList(factory.conPattern(con.constructor.getRef(), subPatterns)), factory.meta("case_" + con.constructor.getName(), new MetaDefinition() {
              @Override
              public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
                ConcreteExpression result = check(new HidingContext(context, Collections.singleton(binding)), null, null, true, marker, typechecker);
                return result == null ? null : typechecker.typecheck(result, contextData.getExpectedType());
              }
            })));
          }
          break;
        }

        RType rType = makeRType(binding, type);
        RType prev = null;
        if (rType instanceof EqType) {
          closure.addRelation(((EqType) rType).leftExpr, ((EqType) rType).rightExpr, factory.ref(binding));
        } else {
          prev = assumptions.putIfAbsent(typeValues.addValue(type), rType);
        }
        if (searchForContradiction && prev == null) {
          makeNegation(type, factory.ref(binding), factory, negations);
        }
      }

      if (contr == null) {
        loop:
        for (Negation negation : negations) {
          List<ConcreteExpression> arguments = new ArrayList<>();
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
                int index = typeValues.getValue(assumption.type.substitute(subst));
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
          typechecker.getErrorReporter().report(new TypecheckingError("Cannot infer contradiction", marker));
          return null;
        }
      }
    }

    return expectedType != null && expectedType.compare(type, CMP.EQ) ? contr : factory.caseExpr(false, Collections.singletonList(factory.caseArg(contr, null, null)), withExpectedType ? null : factory.ref(ext.Empty.getRef()), null, clauses);
  }

  public static boolean isEmpty(CoreExpression type) {
    if (type instanceof CoreDataCallExpression) {
      List<CoreConstructor> constructors = ((CoreDataCallExpression) type).computeMatchedConstructors();
      return constructors != null && constructors.isEmpty();
    }
    return false;
  }
}
