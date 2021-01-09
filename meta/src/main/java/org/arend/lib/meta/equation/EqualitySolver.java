package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.instance.InstanceSearchParameters;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.meta.closure.EquivalenceClosure;
import org.arend.lib.meta.closure.ValuesRelationClosure;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class EqualitySolver extends BaseEqualitySolver {
  private CoreExpression valuesType;
  private EquationSolver algebraSolver;
  private Values<UncheckedExpression> values;

  public EqualitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr) {
    super(meta, typechecker, factory, refExpr, null);
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
  public boolean initializeSolver() {
    if (!initializeAlgebraSolver(valuesType)) {
      values = new Values<>(typechecker, refExpr);
    }
    return true;
  }

  @Override
  public ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter) {
    if (algebraSolver != null) {
      return algebraSolver.solve(hint, leftExpr, rightExpr, errorReporter);
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

  private CoreClassCallExpression getClassCall(CoreExpression type) {
    CoreExpression instanceType = type.normalize(NormalizationMode.WHNF);
    return instanceType instanceof CoreClassCallExpression ? (CoreClassCallExpression) instanceType : null;
  }

  private void initializeAlgebraSolver(TypedExpression instance, CoreClassCallExpression classCall) {
    algebraSolver = classCall.getDefinition().isSubClassOf(meta.Semiring) ? new RingSolver(meta, typechecker, factory, refExpr, equality, instance, classCall) : new MonoidSolver(meta, typechecker, factory, refExpr, equality, instance, classCall);
  }

  private boolean initializeAlgebraSolver(CoreExpression type) {
    type = type == null ? null : type.normalize(NormalizationMode.WHNF);
    if (type instanceof CoreFieldCallExpression) {
      if (((CoreFieldCallExpression) type).getDefinition() == meta.ext.carrier) {
        TypedExpression instance = ((CoreFieldCallExpression) type).getArgument().computeTyped();
        CoreClassCallExpression classCall = getClassCall(instance.getType());
        if (classCall != null && (classCall.getDefinition().isSubClassOf(meta.Monoid) || classCall.getDefinition().isSubClassOf(meta.AddMonoid) || classCall.getDefinition().isSubClassOf(meta.MSemilattice))) {
          initializeAlgebraSolver(instance, classCall);
          return true;
        }
      }
    } else {
      TypedExpression instance = typechecker.findInstance(new InstanceSearchParameters() {
        @Override
        public boolean testClass(@NotNull CoreClassDefinition classDefinition) {
          return classDefinition.isSubClassOf(meta.Monoid) || classDefinition.isSubClassOf(meta.MSemilattice);
        }
      }, type, null, refExpr);
      if (instance != null) {
        CoreClassCallExpression classCall = getClassCall(instance.getType());
        if (classCall != null) {
          initializeAlgebraSolver(instance, classCall);
          return true;
        }
      }
    }

    return false;
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    return algebraSolver != null ? algebraSolver.finalize(result) : typechecker.typecheck(result, null);
  }
}
