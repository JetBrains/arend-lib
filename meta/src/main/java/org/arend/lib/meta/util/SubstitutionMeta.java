package org.arend.lib.meta.util;

import org.arend.ext.concrete.ConcreteFactory;
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

public class SubstitutionMeta implements MetaDefinition {
  private final CoreExpression expression;
  private final LevelSubstitution levelSubst;
  private final List<SubstitutionPair> substitution;

  public SubstitutionMeta(CoreExpression expression, LevelSubstitution levelSubst, List<SubstitutionPair> substitution) {
    this.expression = expression;
    this.levelSubst = levelSubst;
    this.substitution = new ArrayList<>(substitution);
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

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    CoreExpression result = typechecker.substitute(expression, levelSubst, substitution);
    return result == null ? null : result.computeTyped();
  }
}
