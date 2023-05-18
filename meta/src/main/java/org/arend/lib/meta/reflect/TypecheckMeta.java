package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class TypecheckMeta extends BaseMetaDefinition {
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor thisExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor sigmaExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor holeExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor universeExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor tupleExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor classExtExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor newExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor evalExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor goalExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor letExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor piExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor typedExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor localVar;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor globalVar;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor caseExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor projExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor appExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor lamExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor boxExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor numberExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor stringExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor qNameExpr;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor wrapExpr;

  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor stdLevel;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor maxLevel;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor sucLevel;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor numberLevel;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor infLevel;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor varLevel;

  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor pLevel;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor hLevel;

  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor tuplePattern;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor namePattern;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor numberPattern;
  @Dependency(module = "Reflect.ConcreteExpr")  public CoreConstructor conPattern;

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
