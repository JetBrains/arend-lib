package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.instance.InstanceSearchParameters;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.meta.closure.EquivalenceClosure;
import org.arend.lib.meta.closure.ValuesRelationClosure;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class EqualitySolver extends BaseEqualitySolver {
  private CoreExpression valuesType;
  private EquationSolver algebraSolver;
  private Values<UncheckedExpression> values;
  private final CoreClassDefinition forcedClass;
  private final boolean useSolver;

  private EqualitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr, CoreClassDefinition forcedClass, boolean useSolver) {
    super(meta, typechecker, factory, refExpr, null);
    this.forcedClass = forcedClass;
    this.useSolver = useSolver;
  }

  public EqualitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr, CoreClassDefinition forcedClass) {
    this(meta, typechecker, factory, refExpr, forcedClass, true);
  }

  public EqualitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr, boolean useSolver) {
    this(meta, typechecker, factory, refExpr, null, useSolver);
  }

  public EqualitySolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr) {
    this(meta, typechecker, factory, refExpr, null, true);
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
  public void setUseHypotheses(boolean useHypotheses) {
    super.setUseHypotheses(useHypotheses);
    if (algebraSolver instanceof BaseEqualitySolver) {
      ((BaseEqualitySolver) algebraSolver).setUseHypotheses(useHypotheses);
    }
  }

  @Override
  public boolean initializeSolver() {
    if (!initializeAlgebraSolver(valuesType)) {
      values = new Values<>(typechecker, refExpr);
    }
    return true;
  }

  @Override
  public SubexprOccurrences matchSubexpr(@NotNull TypedExpression subExpr, @NotNull TypedExpression expr, @NotNull ErrorReporter errorReporter, List<Integer> occurrences) {
    if (algebraSolver != null) {
      return algebraSolver.matchSubexpr(subExpr, expr, errorReporter, occurrences);
    }
    return super.matchSubexpr(subExpr, expr, errorReporter, occurrences);
  }

  @Override
  public ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter) {
    if (algebraSolver != null) {
      return algebraSolver.solve(hint, leftExpr, rightExpr, errorReporter);
    }

    ValuesRelationClosure closure = new ValuesRelationClosure(values, new EquivalenceClosure<>(factory.ref(meta.ext.prelude.getIdp().getRef()), factory.ref(meta.ext.inv.getRef()), factory.ref(meta.ext.concat.getRef()), factory));
    if (useHypotheses) {
      ContextHelper helper = new ContextHelper(hint);
      for (CoreBinding binding : helper.getAllBindings(typechecker)) {
        CoreFunCallExpression equality = binding.getTypeExpr().normalize(NormalizationMode.WHNF).toEquality();
        if (equality != null && typechecker.compare(equality.getDefCallArguments().get(0), valuesType, CMP.EQ, refExpr, false, true, false)) {
          closure.addRelation(equality.getDefCallArguments().get(1), equality.getDefCallArguments().get(2), factory.ref(binding));
        }
      }
    }
    return closure.checkRelation(leftExpr.getExpression(), rightExpr.getExpression());
  }

  private void initializeAlgebraSolver(TypedExpression instance, CoreClassCallExpression classCall) {
    algebraSolver = meta.Semiring != null && classCall.getDefinition().isSubClassOf(meta.Semiring) && (forcedClass == null || forcedClass.isSubClassOf(meta.Semiring)) || meta.BoundedDistributiveLattice != null && classCall.getDefinition().isSubClassOf(meta.BoundedDistributiveLattice) && (forcedClass == null || forcedClass.isSubClassOf(meta.BoundedDistributiveLattice))
      ? new RingSolver(meta, typechecker, factory, refExpr, equality, instance, classCall, forcedClass, useHypotheses)
      : new MonoidSolver(meta, typechecker, factory, refExpr, equality, instance, classCall, forcedClass, useHypotheses);
  }

  private boolean initializeAlgebraSolver(CoreExpression type) {
    if (!useSolver) {
      return false;
    }

    type = type == null ? null : type.normalize(NormalizationMode.WHNF);

    if (type instanceof CoreAppExpression) {
      CoreExpression typeFun = ((CoreAppExpression) type).getFunction().normalize(NormalizationMode.WHNF);
      if (typeFun instanceof CoreAppExpression) {
        CoreExpression fun = ((CoreAppExpression) typeFun).getFunction().normalize(NormalizationMode.WHNF);
        if (fun instanceof CoreFieldCallExpression) {
          if (((CoreFieldCallExpression) fun).getDefinition() == meta.ext.sipMeta.catHom) {
            algebraSolver = new MonoidSolver(meta, typechecker, factory, refExpr, equality, ((CoreFieldCallExpression) fun).getArgument().computeTyped(), null, null, false);
            return true;
          }
          return false;
        }
      }
    }

    var possibleClasses = new HashSet<>(Arrays.asList(meta.Monoid, meta.AddMonoid, meta.MSemilattice));
    Pair<TypedExpression, CoreClassCallExpression> pair = Utils.findInstanceWithClassCall(new InstanceSearchParameters() {
        @Override
        public boolean testClass(@NotNull CoreClassDefinition classDefinition) {
          if (forcedClass != null && !classDefinition.isSubClassOf(forcedClass)) {
            return false;
          }
          for (var clazz : possibleClasses) {
            if (classDefinition.isSubClassOf(clazz) && (forcedClass == null || forcedClass.isSubClassOf(clazz))) {
              return true;
            }
          }
          return false;
        }
      }, meta.ext.carrier, type, typechecker, refExpr, forcedClass);
    if (pair != null) {
      initializeAlgebraSolver(pair.proj1, pair.proj2);
      return true;
    } else {
      return false;
    }
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    return algebraSolver != null ? algebraSolver.finalize(result) : typechecker.typecheck(result, null);
  }
}
