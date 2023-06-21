package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.expr.*;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class CoreReflectBuilder implements CoreExpressionVisitor<Void, ConcreteExpression> {
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor infVarExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor boxExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor piExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor typeConstructorExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor typeDestructorExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor sigmaExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor appExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor caseExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor projExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor lamExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor dataExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor stringExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor universeExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor pathExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor localVarExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor newExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor pEvalExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor atExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor tupleExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor qNameExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor errorExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor classCallExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor conCallExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor fieldCallExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor defCallExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor arrayExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor letExpr;
  @Dependency(module = "Reflect.CoreExpr")  public CoreConstructor natExpr;

  private final ConcreteFactory factory;
  private final StdExtension ext;
  private final Map<CoreBinding, Integer> localRefs = new HashMap<>();

  public CoreReflectBuilder(ConcreteFactory factory, ExpressionTypechecker typechecker, StdExtension ext) {
    this.factory = factory;
    this.ext = ext;

    List<CoreBinding> bindings = typechecker.getFreeBindingsList();
    for (int i = 0; i < bindings.size(); i++) {
      localRefs.put(bindings.get(i), i);
    }
  }

  private ConcreteExpression makeBool(boolean b) {
    return factory.ref(b ? ext.true_.getRef() : ext.false_.getRef());
  }

  @Override
  public ConcreteExpression visitApp(@NotNull CoreAppExpression expr, Void params) {
    return factory.app(factory.ref(appExpr.getRef()), true, expr.getFunction().accept(this, null), expr.getArgument().accept(this, null), makeBool(expr.isExplicit()));
  }

  @Override
  public ConcreteExpression visitFunCall(@NotNull CoreFunCallExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitConCall(@NotNull CoreConCallExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitDataCall(@NotNull CoreDataCallExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitFieldCall(@NotNull CoreFieldCallExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitClassCall(@NotNull CoreClassCallExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitReference(@NotNull CoreReferenceExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitInferenceReference(@NotNull CoreInferenceReferenceExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitLam(@NotNull CoreLamExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitPi(@NotNull CorePiExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitSigma(@NotNull CoreSigmaExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitUniverse(@NotNull CoreUniverseExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitError(@NotNull CoreErrorExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitTuple(@NotNull CoreTupleExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitProj(@NotNull CoreProjExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitNew(@NotNull CoreNewExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitPEval(@NotNull CorePEvalExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitBox(@NotNull CoreBoxExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitLet(@NotNull CoreLetExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitCase(@NotNull CoreCaseExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitInteger(@NotNull CoreIntegerExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitString(@NotNull CoreStringExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitQName(@NotNull CoreQNameExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitTypeConstructor(@NotNull CoreTypeConstructorExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitTypeDestructor(@NotNull CoreTypeDestructorExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitArray(@NotNull CoreArrayExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitPath(@NotNull CorePathExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitAt(@NotNull CoreAtExpression expr, Void params) {
    return null;
  }
}
