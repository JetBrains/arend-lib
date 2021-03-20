package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.instance.InstanceSearchParameters;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.key.FieldKey;
import org.arend.lib.meta.closure.EquivalenceClosure;
import org.arend.lib.meta.closure.ValuesRelationClosure;
import org.arend.lib.util.Lazy;
import org.arend.lib.util.Maybe;
import org.arend.lib.util.Values;
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

  private static class RelationData {
    final CoreDefCallExpression defCall;
    final CoreExpression leftExpr;
    final CoreExpression rightExpr;

    private RelationData(CoreDefCallExpression defCall, CoreExpression leftExpr, CoreExpression rightExpr) {
      this.defCall = defCall;
      this.leftExpr = leftExpr;
      this.rightExpr = rightExpr;
    }
  }

  private RelationData getRelationData(CoreExpression type) {
    if (type instanceof CoreDefCallExpression) {
      CoreDefCallExpression defCall = (CoreDefCallExpression) type;
      if (instanceDefinition != null && defCall.getDefinition() != instanceDefinition) {
        return null;
      }

      if (defCall instanceof CoreClassCallExpression) {
        var impls = ((CoreClassCallExpression) defCall).getImplementations();
        if (impls.size() != 2) {
          return null;
        }
        var it = impls.iterator();
        return new RelationData(defCall, it.next().getValue(), it.next().getValue());
      } else {
        if (defCall.getDefCallArguments().size() < 2) {
          return null;
        }
        return new RelationData(defCall, defCall.getDefCallArguments().get(defCall.getDefCallArguments().size() - 2), defCall.getDefCallArguments().get(defCall.getDefCallArguments().size() - 1));
      }
    }

    if (!(type instanceof CoreAppExpression)) {
      return null;
    }

    CoreAppExpression app2 = (CoreAppExpression) type;
    CoreExpression fun2 = app2.getFunction().normalize(NormalizationMode.WHNF);
    if (!(fun2 instanceof CoreAppExpression)) {
      return null;
    }

    CoreAppExpression app1 = (CoreAppExpression) fun2;
    CoreExpression fun1 = app1.getFunction().normalize(NormalizationMode.WHNF);
    if (!(fun1 instanceof CoreFieldCallExpression) || instanceDefinition != null && ((CoreFieldCallExpression) fun1).getDefinition() != instanceDefinition) {
      return null;
    }

    return new RelationData((CoreFieldCallExpression) fun1, app1.getArgument(), app2.getArgument());
  }

  private class MyInstanceSearchParameters implements InstanceSearchParameters {
    private final CoreDefinition definition;
    private final List<CoreClassField> relationFields = new ArrayList<>();
    private CoreClassField relationField;

    private MyInstanceSearchParameters(CoreDefinition definition) {
      this.definition = definition;
    }

    @Override
    public boolean searchLocal() {
      return false;
    }

    @Override
    public boolean testClass(@NotNull CoreClassDefinition classDefinition) {
      relationFields.clear();
      for (CoreClassField field : classDefinition.getFields()) {
        transFieldData = field.getUserData(meta.ext.transitivityKey);
        if (transFieldData != null) {
          relationFields.add(field);
        }
      }
      return !relationFields.isEmpty();
    }

    @Override
    public boolean testGlobalInstance(@NotNull CoreFunctionDefinition instance) {
      if (!(instance.getResultType() instanceof CoreClassCallExpression)) {
        return false;
      }

      for (CoreClassField relationField : relationFields) {
        CoreAbsExpression absImpl = ((CoreClassCallExpression) instance.getResultType()).getAbsImplementation(relationField);
        if (absImpl == null) {
          continue;
        }
        CoreExpression impl = absImpl.getExpression();
        if (!(impl instanceof CoreLamExpression)) {
          continue;
        }

        CoreParameter param1 = ((CoreLamExpression) impl).getParameters();
        CoreParameter param2 = param1.getNext();
        CoreExpression body = ((CoreLamExpression) impl).getBody();
        if (!param2.hasNext()) {
          if (!(body instanceof CoreLamExpression)) {
            continue;
          }
          param2 = ((CoreLamExpression) body).getParameters();
          body = ((CoreLamExpression) body).getBody();
        }
        if (param2.getNext().hasNext()) {
          continue;
        }

        if (!(body instanceof CoreDefCallExpression)) {
          continue;
        }
        CoreDefCallExpression defCall = (CoreDefCallExpression) body;
        var args = defCall.getDefCallArguments();
        if (defCall.getDefinition() == definition && args.size() >= 2 && args.get(args.size() - 2) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(args.size() - 2)).getBinding() == param1.getBinding() && args.get(args.size() - 1) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(args.size() - 1)).getBinding() == param2.getBinding()) {
          this.relationField = relationField;
          return true;
        }
      }

      return false;
    }
  }

  @Override
  public boolean isApplicable(CoreExpression type) {
    RelationData relationData = getRelationData(type);
    if (relationData == null) {
      return false;
    }

    leftValue = relationData.leftExpr;
    rightValue = relationData.rightExpr;
    if (relationData.defCall instanceof CoreFieldCallExpression) {
      CoreFieldCallExpression fieldCall = (CoreFieldCallExpression) relationData.defCall;
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
          meta.transitivityInstanceCache.put(defCall.getDefinition(), new EquationMeta.TransitivityInstanceCache(((CoreFunCallExpression) instance.getExpression()).getDefinition(), parameters.relationField));
        }
        relationField = parameters.relationField;
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
      RelationData relationData = getRelationData(binding.getTypeExpr().normalize(NormalizationMode.WHNF));
      if (relationData != null) {
        closure.addRelation(relationData.leftExpr, relationData.rightExpr, factory.ref(binding));
      }
    }
    return closure.checkRelation(leftExpr.getExpression(), rightExpr.getExpression());
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    return typechecker.typecheck(result, null);
  }
}
