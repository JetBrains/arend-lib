package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CorePiExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.RewriteMeta;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Collections;

public abstract class LocalSimplificationRuleBase implements SimplificationRule {
  protected final ConcreteFactory factory;
  protected final StdExtension ext;
  protected final ConcreteReferenceExpression refExpr;
  protected final ExpressionTypechecker typechecker;
  protected final CoreClassCallExpression classCall;
  protected final TypedExpression instance;

  public LocalSimplificationRuleBase(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ConcreteReferenceExpression refExpr, ExpressionTypechecker typechecker) {
    this.ext = ext;
    this.factory = ext.factory;
    this.refExpr = refExpr;
    this.typechecker = typechecker;
    this.classCall = classCall;
    this.instance = instance;
  }

  @Override
  public ConcreteExpression finalizeEqProof(ConcreteExpression proof) { return proof; }

  @Override
  public RewriteMeta.EqProofConcrete apply(TypedExpression expression) {
    var simplifiedExpression = expression;
    RewriteMeta.EqProofConcrete simplificationProof = null;
    while (true) {
      typechecker.checkCancelled();
      final RewriteMeta.EqProofConcrete[] simplificationRes = {null};
      TypedExpression finalSimplifiedExpression = simplifiedExpression;
      simplifiedExpression.getExpression().processSubexpression(subexpr -> {
        if (!subexpr.computeType().compare(expression.getType(), CMP.EQ)) {
          if (subexpr.computeType() instanceof CorePiExpression) {
            var type = (CorePiExpression)subexpr.computeType();
            var params = type.getParameters();
            while (true) {
              if (!params.getBinding().getTypeExpr().compare(expression.getType(), CMP.EQ)) {
                return CoreExpression.FindAction.SKIP;
              }
              if (params.hasNext()) break;
              params = params.getNext();
            }
            if (!type.getCodomain().compare(expression.getType(), CMP.EQ)) {
              return CoreExpression.FindAction.SKIP;
            }
          } else {
            return CoreExpression.FindAction.SKIP;
          }
        }
        simplificationRes[0] = applySimplificationToSubexpr(finalSimplifiedExpression, subexpr);
        if (simplificationRes[0] != null) {
          return CoreExpression.FindAction.STOP;
        }
        return CoreExpression.FindAction.CONTINUE;
      });
      if (simplificationRes[0] != null) {
        simplifiedExpression = typechecker.typecheck(simplificationRes[0].right, expression.getType());
        if (simplifiedExpression == null) {
          return null;
        }
        if (simplificationProof == null) {
          simplificationProof = simplificationRes[0];
          continue;
        }
        simplificationProof.right = simplificationRes[0].right;
        simplificationProof.proof = factory.appBuilder(factory.ref(ext.concat.getRef())).app(simplificationProof.proof).app(simplificationRes[0].proof).build();
        continue;
      }
      break;
    }
    return simplificationProof;
  }

  protected abstract Pair<CoreExpression, ConcreteExpression> simplifySubexpression(CoreExpression subexpr);

  private RewriteMeta.EqProofConcrete applySimplificationToSubexpr(TypedExpression expr, CoreExpression subexpr) {
    var simplifyRes = simplifySubexpression(subexpr);
    if (simplifyRes != null) {
      var var = factory.local("i");
      var typeParam = factory.ref(ext.prelude.getInterval().getRef());
      ConcreteExpression lam = factory.lam(Collections.singletonList(factory.param(true, Collections.singletonList(var), typeParam)),
              factory.meta("\\lam i => {!}", new MetaDefinition() {
                @Override
                public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
                  var checkedVar =  typechecker.typecheck(factory.ref(var), null);
                  if (checkedVar == null) return null;
                  var exprWithInterval = expr.getExpression().replaceSubexpressions(expression -> {
                    if (expression == subexpr) {
                      var ideElimPath = factory.at(simplifyRes.proj2, factory.core(checkedVar));
                      var checkedPath = typechecker.typecheck(ideElimPath, null);
                      if (checkedPath == null) return null;
                      return checkedPath.getExpression();
                    }
                    return null;
                  }, false);
                  return exprWithInterval != null ? Utils.tryTypecheck(typechecker, tc -> tc.check(exprWithInterval, refExpr)) : null;
                }}));
      var simplifiedExpr = expr.getExpression().replaceSubexpressions(expression -> {
        if (expression == subexpr) {
          return simplifyRes.proj1;
        }
        return null;
      }, true);
      if (simplifiedExpr == null) return null;
      var checkedLam = typechecker.typecheck(lam, null);
      if (checkedLam == null) return null;
      var exprPath = factory.path(factory.core(checkedLam));
      var checkedSimplifiedExpr = typechecker.check(simplifiedExpr, refExpr);
      if (checkedSimplifiedExpr == null) return null;
      return new RewriteMeta.EqProofConcrete(exprPath, factory.core(expr), factory.core(checkedSimplifiedExpr));
    }
    return null;
  }
}
