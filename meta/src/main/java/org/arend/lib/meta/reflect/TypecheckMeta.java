package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class TypecheckMeta extends BaseMetaDefinition {
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor thisExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor sigmaExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor holeExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor universeExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor tupleExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor classExtExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor evalExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor goalExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor letExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor piExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor typedExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor localVar;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor globalVar;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor caseExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor projExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor appExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor lamExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor boxExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor numberExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor stringExpr;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor qNameExpr;

  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor stdLevel;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor maxLevel;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor sucLevel;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor numberLevel;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor infLevel;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor varLevel;

  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor pLevel;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor hLevel;

  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor tuplePattern;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor namePattern;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor numberPattern;
  @Dependency(module = "Meta.ConcreteExpr")   public CoreConstructor conPattern;

  final StdExtension ext;

  public TypecheckMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    TypedExpression arg = typechecker.typecheck(contextData.getArguments().get(0).getExpression(), null);
    if (arg == null) return null;
    ConcreteExpression result = new TypecheckBuilder(this, ext.factory.withData(contextData.getMarker()), typechecker, contextData.getMarker()).process(arg.getExpression());
    return result == null ? null : typechecker.typecheck(result, contextData.getExpectedType());
  }
}
