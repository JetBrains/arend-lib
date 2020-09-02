package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.meta.closure.EquivalenceClosure;
import org.arend.lib.meta.closure.ValuesRelationClosure;
import org.arend.lib.util.Maybe;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class EqualitySolver implements EquationSolver {
  private final EquationMeta meta;
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;
  private final ConcreteReferenceExpression refExpr;
  private CoreExpression valuesType;
  private CoreFunCallExpression equality;
  private MonoidSolver monoidSolver;
  private Values<UncheckedExpression> values;

  public EqualitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr) {
    this.meta = meta;
    this.typechecker = typechecker;
    this.factory = factory;
    this.refExpr = refExpr;
  }

  @Override
  public boolean isApplicable(CoreExpression type) {
    equality = type.toEquality();
    if (equality == null) {
      return false;
    }
    setValuesType(equality.getDefCallArguments().get(0));
    return true;
  }

  @Override
  public CoreExpression getValuesType() {
    return valuesType;
  }

  public void setValuesType(CoreExpression type) {
    valuesType = type;
  }

  @Override
  public CoreExpression getLeftValue() {
    return equality == null ? null : equality.getDefCallArguments().get(1);
  }

  @Override
  public CoreExpression getRightValue() {
    return equality == null ? null : equality.getDefCallArguments().get(2);
  }

  @Override
  public @Nullable Maybe<CoreExpression> getEqType(@Nullable TypedExpression leftExpr, @Nullable TypedExpression rightExpr) {
    if (leftExpr != null && rightExpr != null) {
      TypedExpression result = typechecker.typecheck(factory.app(factory.ref(meta.ext.prelude.getEquality().getRef()), true, Arrays.asList(factory.core(null, leftExpr), factory.core(null, rightExpr))), null);
      return result == null ? null : new Maybe<>(result.getExpression());
    } else {
      return new Maybe<>(null);
    }
  }

  @Override
  public TypedExpression getTrivialResult(TypedExpression expression) {
    return typechecker.typecheck(factory.app(factory.ref(meta.ext.prelude.getIdp().getRef()), false, Arrays.asList(factory.hole(), factory.core(null, expression))), null);
  }

  @Override
  public ConcreteExpression combineResults(ConcreteExpression expr1, ConcreteExpression expr2) {
    return factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(expr1, expr2));
  }

  @Override
  public boolean isHint(ConcreteExpression expression) {
    return ContextHelper.getMeta(expression) != null;
  }

  @Override
  public boolean initializeSolver() {
    CoreClassDefinition classDef = getClassDef(valuesType);
    if (classDef != null) {
      monoidSolver = new MonoidSolver(meta, typechecker, factory, refExpr, equality, classDef);
    } else {
      values = new Values<>(typechecker, refExpr);
    }
    return true;
  }

  @Override
  public ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter) {
    if (monoidSolver != null) {
      return monoidSolver.solve(hint, leftExpr, rightExpr, errorReporter);
    }

    ValuesRelationClosure closure = new ValuesRelationClosure(values, new EquivalenceClosure<>(factory.ref(meta.ext.prelude.getIdp().getRef()), factory.ref(meta.ext.inv.getRef()), factory.ref(meta.ext.concat.getRef()), factory));
    ContextHelper helper = new ContextHelper(hint);
    for (CoreBinding binding : helper.getAllBindings(typechecker)) {
      CoreFunCallExpression equality = binding.getTypeExpr().normalize(NormalizationMode.WHNF).toEquality();
      if (equality != null) {
        closure.addRelation(equality.getDefCallArguments().get(1), equality.getDefCallArguments().get(2), factory.ref(binding));
      }
    }
    return closure.checkRelation(leftExpr.getExpression(), rightExpr.getExpression());
  }

  private CoreClassDefinition getClassDef(CoreExpression type) {
    type = type == null ? null : type.normalize(NormalizationMode.WHNF);
    if (type instanceof CoreFieldCallExpression) {
      if (((CoreFieldCallExpression) type).getDefinition() == meta.carrier) {
        CoreExpression instanceType = ((CoreFieldCallExpression) type).getArgument().computeType().normalize(NormalizationMode.WHNF);
        if (instanceType instanceof CoreClassCallExpression) {
          CoreClassDefinition classDef = ((CoreClassCallExpression) instanceType).getDefinition();
          if (classDef.isSubClassOf(meta.Monoid)) {
            return classDef;
          }
        }
      }
    }

    return null;
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    return monoidSolver != null ? monoidSolver.finalize(result) : typechecker.typecheck(result, null);
  }
}
