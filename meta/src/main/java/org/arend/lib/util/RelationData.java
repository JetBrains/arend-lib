package org.arend.lib.util;

import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;

public class RelationData {
  public final CoreDefCallExpression defCall;
  public final CoreExpression leftExpr;
  public final CoreExpression rightExpr;

  public RelationData(CoreDefCallExpression defCall, CoreExpression leftExpr, CoreExpression rightExpr) {
    this.defCall = defCall;
    this.leftExpr = leftExpr;
    this.rightExpr = rightExpr;
  }

  public static RelationData getRelationData(CoreExpression type) {
    if (type instanceof CoreDefCallExpression) {
      CoreDefCallExpression defCall = (CoreDefCallExpression) type;
      if (defCall instanceof CoreClassCallExpression) {
        var impls = ((CoreClassCallExpression) defCall).getImplementations();
        if (impls.size() != 2) {
          return null;
        }
        var it = impls.iterator();
        return new RelationData(defCall, it.next().getValue(), it.next().getValue());
      } else {
        if (defCall.getDefCallArguments().size() < 2) {
          return null;
        }
        return new RelationData(defCall, defCall.getDefCallArguments().get(defCall.getDefCallArguments().size() - 2), defCall.getDefCallArguments().get(defCall.getDefCallArguments().size() - 1));
      }
    }

    if (!(type instanceof CoreAppExpression)) {
      return null;
    }

    CoreAppExpression app2 = (CoreAppExpression) type;
    CoreExpression fun2 = app2.getFunction().normalize(NormalizationMode.WHNF);
    if (!(fun2 instanceof CoreAppExpression)) {
      return null;
    }

    CoreAppExpression app1 = (CoreAppExpression) fun2;
    CoreExpression fun1 = app1.getFunction().normalize(NormalizationMode.WHNF);
    return fun1 instanceof CoreFieldCallExpression ? new RelationData((CoreFieldCallExpression) fun1, app1.getArgument(), app2.getArgument()) : null;
  }
}
