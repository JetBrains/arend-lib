package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.key.FieldKey;
import org.arend.lib.meta.closure.EquivalenceClosure;
import org.arend.lib.meta.closure.ValuesRelationClosure;
import org.arend.lib.util.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class TransitivitySolver implements EquationSolver {
  private final EquationMeta meta;
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;
  private final ConcreteExpression refExpr;

  private Lazy<ConcreteExpression> relation;
  private FieldKey.Data reflFieldData;
  private FieldKey.Data transFieldData;
  private ConcreteExpression trans;
  private Lazy<CoreExpression> valuesType;
  private CoreExpression leftValue;
  private CoreExpression rightValue;
  private CoreDefinition instanceDefinition;

  private Values<UncheckedExpression> values;

  public TransitivitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteExpression refExpr) {
    this.meta = meta;
    this.typechecker = typechecker;
    this.factory = factory;
    this.refExpr = refExpr;
  }

  private class MyInstanceSearchParameters extends DefImplInstanceSearchParameters {
    private MyInstanceSearchParameters(CoreDefinition definition) {
      super(definition);
    }

    @Override
    protected List<CoreClassField> getRelationFields(CoreClassDefinition classDef) {
      List<CoreClassField> relationFields = Collections.emptyList();
      for (CoreClassField field : classDef.getNotImplementedFields()) {
        transFieldData = field.getUserData(meta.ext.transitivityKey);
        if (transFieldData != null) {
          if (relationFields.isEmpty()) relationFields = new ArrayList<>();
          relationFields.add(field);
        }
      }
      for (CoreClassField field : classDef.getImplementedFields()) {
        transFieldData = field.getUserData(meta.ext.transitivityKey);
        if (transFieldData != null) {
          if (relationFields.isEmpty()) relationFields = new ArrayList<>();
          relationFields.add(field);
        }
      }
      return relationFields;
    }
  }

  @Override
  public boolean isApplicable(CoreExpression type) {
    RelationData relationData = RelationData.getRelationData(type);
    if (relationData == null || instanceDefinition != null && relationData.defCall.getDefinition() != instanceDefinition) {
      return false;
    }

    leftValue = relationData.leftExpr;
    rightValue = relationData.rightExpr;
    if (relationData.defCall instanceof CoreFieldCallExpression fieldCall) {
      transFieldData = fieldCall.getDefinition().getUserData(meta.ext.transitivityKey);
      if (transFieldData == null) {
        return false;
      }

      reflFieldData = fieldCall.getDefinition().getUserData(meta.ext.reflexivityKey);
      relation = new Lazy<>(() -> factory.core(fieldCall.computeTyped()));
      valuesType = new Lazy<>(() -> {
        TypedExpression instance = fieldCall.getArgument().computeTyped();
        if (instance.getType() instanceof CoreClassCallExpression) {
          CoreExpression result = ((CoreClassCallExpression) instance.getType()).getImplementation(meta.ext.carrier, instance);
          if (result != null) {
            return result;
          }
        }
        return Objects.requireNonNull(typechecker.typecheck(factory.app(factory.ref(meta.ext.carrier.getRef()), false, Collections.singletonList(factory.core(instance))), null)).getExpression();
      });
      instanceDefinition = fieldCall.getDefinition();
    } else {
      CoreDefCallExpression defCall = relationData.defCall;
      EquationMeta.TransitivityInstanceCache cache = meta.transitivityInstanceCache.get(defCall.getDefinition());
      CoreClassField relationField;
      TypedExpression instance;
      if (cache != null) {
        List<ConcreteExpression> args = new ArrayList<>();
        for (CoreParameter param = cache.instance.getParameters(); param.hasNext(); param = param.getNext()) {
          if (param.isExplicit()) {
            args.add(factory.hole());
          }
        }
        instance = typechecker.typecheck(factory.app(factory.ref(cache.instance.getRef()), true, args), null);
        relationField = cache.relationField;
      } else {
        MyInstanceSearchParameters parameters = new MyInstanceSearchParameters(defCall.getDefinition());
        instance = typechecker.findInstance(parameters, null, null, refExpr);
        if (instance != null && instance.getExpression() instanceof CoreFunCallExpression) {
          meta.transitivityInstanceCache.put(defCall.getDefinition(), new EquationMeta.TransitivityInstanceCache(((CoreFunCallExpression) instance.getExpression()).getDefinition(), parameters.getRelationField()));
        }
        relationField = parameters.getRelationField();
      }

      if (instance == null || !(instance.getType() instanceof CoreClassCallExpression)) {
        return false;
      }

      transFieldData = relationField.getUserData(meta.ext.transitivityKey);
      reflFieldData = relationField.getUserData(meta.ext.reflexivityKey);
      relation = new Lazy<>(() -> factory.core(Objects.requireNonNull(((CoreClassCallExpression) instance.getType()).getImplementation(relationField, instance)).computeTyped()));
      valuesType = new Lazy<>(() -> ((CoreClassCallExpression) instance.getType()).getImplementation(meta.ext.carrier, instance));
      instanceDefinition = defCall.getDefinition();
    }

    List<ConcreteArgument> args = new ArrayList<>(3);
    for (int i = 0; i < 3; i++) {
      if (transFieldData.parametersExplicitness.get(i)) {
        args.add(factory.arg(factory.hole(), true));
      }
    }
    trans = factory.app(factory.ref(transFieldData.field.getRef()), args);

    return true;
  }

  @Override
  public CoreExpression getValuesType() {
    return valuesType.get();
  }

  @Override
  public CoreExpression getLeftValue() {
    return leftValue;
  }

  @Override
  public CoreExpression getRightValue() {
    return rightValue;
  }

  @Override
  public @Nullable Maybe<CoreExpression> getEqType(@Nullable TypedExpression leftExpr, @Nullable TypedExpression rightExpr) {
    if (leftExpr != null && rightExpr != null) {
      TypedExpression result = typechecker.typecheck(factory.app(relation.get(), true, Arrays.asList(factory.core(null, leftExpr), factory.core(null, rightExpr))), null);
      return result == null ? null : new Maybe<>(result.getExpression());
    } else {
      return new Maybe<>(null);
    }
  }

  @Override
  public TypedExpression getTrivialResult(TypedExpression expression) {
    if (reflFieldData == null) {
      return null;
    }

    List<ConcreteArgument> args = new ArrayList<>(2);
    if (!reflFieldData.parametersExplicitness.get(0)) {
      args.add(factory.arg(factory.hole(), false));
    }
    args.add(factory.arg(factory.core(expression), reflFieldData.parametersExplicitness.get(0)));
    return typechecker.typecheck(factory.app(factory.ref(reflFieldData.field.getRef()), args), null);
  }

  @Override
  public ConcreteExpression combineResults(ConcreteExpression expr1, ConcreteExpression expr2) {
    List<ConcreteArgument> args = new ArrayList<>(2);
    args.add(factory.arg(expr1, transFieldData.parametersExplicitness.get(3)));
    args.add(factory.arg(expr2, transFieldData.parametersExplicitness.get(4)));
    return factory.app(trans, args);
  }

  @Override
  public boolean isHint(ConcreteExpression expression) {
    return ContextHelper.getMeta(expression) != null;
  }

  @Override
  public boolean initializeSolver() {
    values = new Values<>(typechecker, refExpr);
    return true;
  }

  @Override
  public ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter) {
    ConcreteExpression reflExpr = null;
    if (reflFieldData != null) {
      reflExpr = factory.ref(reflFieldData.field.getRef());
      if (reflFieldData.parametersExplicitness.get(0)) {
        reflExpr = factory.app(reflExpr, true, Collections.singletonList(factory.hole()));
      }
    }

    ValuesRelationClosure closure = new ValuesRelationClosure(values, new EquivalenceClosure<>(reflExpr, null, trans, factory));
    ContextHelper helper = new ContextHelper(hint);
    for (CoreBinding binding : helper.getAllBindings(typechecker)) {
      RelationData relationData = RelationData.getRelationData(binding.getTypeExpr().normalize(NormalizationMode.WHNF));
      if (relationData != null && (instanceDefinition == null || relationData.defCall.getDefinition() == instanceDefinition)) {
        closure.addRelation(relationData.leftExpr, relationData.rightExpr, factory.ref(binding));
      }
    }
    return closure.checkRelation(leftExpr.getExpression(), rightExpr.getExpression());
  }

  @Override
  public SubexprOccurrences matchSubexpr(@NotNull TypedExpression subExpr, @NotNull TypedExpression expr, @NotNull ErrorReporter errorReporter, List<Integer> occurrences) {
    return null;
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    return typechecker.typecheck(result, null);
  }
}
