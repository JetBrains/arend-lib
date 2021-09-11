package org.arend.lib.meta.util;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.level.LevelSubstitution;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;

public class SubstitutionMeta implements MetaDefinition {
  private final CoreExpression expression;
  private final LevelSubstitution levelSubst;
  private final List<SubstitutionPair> substitution;
  private final Function<CoreExpression, ConcreteExpression> operationOnExpr;

  public SubstitutionMeta(CoreExpression expression, LevelSubstitution levelSubst, List<SubstitutionPair> substitution) {
    this.expression = expression;
    this.levelSubst = levelSubst;
    this.substitution = new ArrayList<>(substitution);
    this.operationOnExpr = null;
  }

  public SubstitutionMeta(CoreExpression expression, LevelSubstitution levelSubst, List<SubstitutionPair> substitution, Function<CoreExpression, ConcreteExpression> operationOnExpr) {
    this.expression = expression;
    this.levelSubst = levelSubst;
    this.substitution = new ArrayList<>(substitution);
    this.operationOnExpr = operationOnExpr;
  }

  public SubstitutionMeta(CoreExpression expression, List<SubstitutionPair> substitution) {
    this(expression, LevelSubstitution.EMPTY, substitution);
  }

  public SubstitutionMeta(CoreExpression expression, CoreBinding binding, ConcreteExpression expr) {
    this(expression, Collections.singletonList(new SubstitutionPair(binding, expr)));
  }

  public static ConcreteExpression makeLambda(CoreExpression expr, CoreBinding binding, ConcreteFactory factory) {
    ArendRef ref = factory.local("x");
    return factory.lam(Collections.singletonList(factory.param(ref)), factory.meta("substitution_meta", new SubstitutionMeta(expr, binding, factory.ref(ref))));
  }

  public static ConcreteExpression makeLambda(CoreExpression expr, List<CoreBinding> coreBindings, ConcreteFactory factory, Function<CoreExpression, ConcreteExpression> operationOnExpr) {
    List<SubstitutionPair> subst = new ArrayList<>();
    List<ConcreteParameter> paramList = new ArrayList<>();
    for (int v = 0; v < coreBindings.size(); ++v) {
      ArendRef ref = factory.local("x" + v);
      subst.add(new SubstitutionPair(coreBindings.get(v), factory.ref(ref)));
      paramList.add(factory.param(ref));
    }
    return factory.lam(paramList, factory.meta("substitution_meta", new SubstitutionMeta(expr, LevelSubstitution.EMPTY, subst, operationOnExpr)));
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    CoreExpression result = typechecker.substitute(expression, levelSubst, substitution);
    if (result == null) return null;
    if (operationOnExpr == null) {
      return result.computeTyped();
    }
    return typechecker.typecheck(operationOnExpr.apply(result), null);
  }
}
