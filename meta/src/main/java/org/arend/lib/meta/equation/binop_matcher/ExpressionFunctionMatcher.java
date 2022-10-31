package org.arend.lib.meta.equation.binop_matcher;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreInferenceReferenceExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;

import java.util.ArrayList;
import java.util.List;

public class ExpressionFunctionMatcher implements FunctionMatcher {
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;
  private final ConcreteSourceNode marker;
  private final TypedExpression mulTyped;
  private final CoreExpression carrierExpr;
  private final int numberOfArguments;

  public ExpressionFunctionMatcher(ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteSourceNode marker, TypedExpression mulTyped, CoreExpression carrierExpr, int numberOfArguments) {
    this.typechecker = typechecker;
    this.factory = factory;
    this.marker = marker;
    this.mulTyped = mulTyped;
    this.carrierExpr = carrierExpr;
    this.numberOfArguments = numberOfArguments;
  }

  @Override
  public List<CoreExpression> match(CoreExpression expr) {
    return typechecker.withCurrentState(tc -> {
      List<CoreInferenceReferenceExpression> varExprs = new ArrayList<>(numberOfArguments);
      List<ConcreteExpression> concreteExprs = new ArrayList<>(numberOfArguments);
      for (int i = 0; i < numberOfArguments; i++) {
        CoreInferenceReferenceExpression varExpr = typechecker.generateNewInferenceVariable("var" + (i + 1), carrierExpr, marker, true);
        varExprs.add(varExpr);
        concreteExprs.add(factory.core(varExpr.computeTyped()));
      }
      TypedExpression result = tc.typecheck(factory.app(factory.core(mulTyped), true, concreteExprs), null);
      boolean ok = result != null && tc.compare(result.getExpression(), expr, CMP.EQ, marker, false, true, false);
      if (ok) {
        for (CoreInferenceReferenceExpression varExpr : varExprs) {
          if (varExpr.getSubstExpression() == null) {
            ok = false;
            break;
          }
        }
      }
      if (ok) {
        List<CoreExpression> args = new ArrayList<>(numberOfArguments);
        for (CoreInferenceReferenceExpression varExpr : varExprs) {
          args.add(varExpr.getSubstExpression());
        }
        return args;
      } else {
        tc.loadSavedState();
        return null;
      }
    });
  }
}
