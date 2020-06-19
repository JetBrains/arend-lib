package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.CoreAppExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFieldCallExpression;
import org.arend.ext.core.expr.UncheckedExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.key.FieldKey;
import org.arend.lib.meta.closure.EquivalenceClosure;
import org.arend.lib.meta.closure.ValuesRelationClosure;
import org.arend.lib.util.Maybe;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class TransitivitySolver implements EquationSolver {
  private final EquationMeta meta;
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;
  private final ConcreteExpression refExpr;

  private ConcreteExpression relation;
  private FieldKey.Data reflFieldData;
  private FieldKey.Data transFieldData;
  private ConcreteExpression trans;
  private CoreExpression valuesType;
  private CoreExpression leftValue;
  private CoreExpression rightValue;

  private Values<UncheckedExpression> values;

  public TransitivitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteExpression refExpr) {
    this.meta = meta;
    this.typechecker = typechecker;
    this.factory = factory;
    this.refExpr = refExpr;
  }

  private static class RelationData {
    final CoreFieldCallExpression fieldCall;
    final CoreExpression leftExpr;
    final CoreExpression rightExpr;

    private RelationData(CoreFieldCallExpression fieldCall, CoreExpression leftExpr, CoreExpression rightExpr) {
      this.fieldCall = fieldCall;
      this.leftExpr = leftExpr;
      this.rightExpr = rightExpr;
    }
  }

  private RelationData getRelationData(CoreExpression type) {
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
    if (!(fun1 instanceof CoreFieldCallExpression)) {
      return null;
    }

    return new RelationData((CoreFieldCallExpression) fun1, app1.getArgument(), app2.getArgument());
  }

  @Override
  public boolean isApplicable(CoreExpression type) {
    RelationData relationData = getRelationData(type);
    if (relationData == null) {
      return false;
    }

    transFieldData = relationData.fieldCall.getDefinition().getUserData(meta.ext.transitivityKey);
    if (transFieldData == null) {
      return false;
    }

    List<ConcreteArgument> args = new ArrayList<>(3);
    for (int i = 0; i < 3; i++) {
      if (transFieldData.parametersExplicitness.get(i)) {
        args.add(factory.arg(factory.hole(), true));
      }
    }
    trans = factory.app(factory.ref(transFieldData.field.getRef()), args);

    reflFieldData = relationData.fieldCall.getDefinition().getUserData(meta.ext.reflexivityKey);
    relation = factory.core(relationData.fieldCall.computeTyped());
    valuesType = relationData.fieldCall.getArgument();
    leftValue = relationData.leftExpr;
    rightValue = relationData.rightExpr;
    return true;
  }

  @Override
  public CoreExpression getValuesType() {
    return valuesType;
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
      TypedExpression result = typechecker.typecheck(factory.app(relation, true, Arrays.asList(factory.core(null, leftExpr), factory.core(null, rightExpr))), null);
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
