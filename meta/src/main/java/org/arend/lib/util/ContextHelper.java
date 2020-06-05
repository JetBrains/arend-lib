package org.arend.lib.util;

import org.arend.ext.concrete.expr.ConcreteAppExpression;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteGoalExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.MetaRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.lib.meta.HidingMeta;
import org.arend.lib.meta.UsingMeta;

import java.util.Collections;
import java.util.List;

public class ContextHelper {
  public final MetaDefinition meta;
  public final ConcreteExpression argument;

  public ContextHelper(ConcreteExpression hint) {
    meta = getMeta(hint);
    if (meta != null) {
      ConcreteExpression expr = hint instanceof ConcreteGoalExpression ? ((ConcreteGoalExpression) hint).getExpression() : hint;
      assert expr != null;
      argument = ((ConcreteAppExpression) expr).getArguments().get(0).getExpression();
    } else {
      argument = null;
    }
  }

  public static MetaDefinition getMeta(ConcreteExpression expr) {
    ConcreteExpression expression = expr instanceof ConcreteGoalExpression ? ((ConcreteGoalExpression) expr).getExpression() : expr;
    if (!(expression instanceof ConcreteAppExpression)) {
      return null;
    }
    ConcreteAppExpression appExpr = (ConcreteAppExpression) expression;
    if (appExpr.getArguments().size() != 1 || !(appExpr.getFunction() instanceof ConcreteReferenceExpression)) {
      return null;
    }
    ArendRef ref = ((ConcreteReferenceExpression) appExpr.getFunction()).getReferent();
    MetaDefinition metaDef = ref instanceof MetaRef ? ((MetaRef) ref).getDefinition() : null;
    return metaDef instanceof UsingMeta || metaDef instanceof HidingMeta ? metaDef : null;
  }

  public List<CoreBinding> getContextBindings(ExpressionTypechecker typechecker) {
    return meta instanceof HidingMeta
      ? HidingMeta.updateBindings(argument, typechecker)
      : meta instanceof UsingMeta && !((UsingMeta) meta).keepOldContext
        ? Collections.emptyList()
        : typechecker.getFreeBindingsList();
  }

  public List<CoreBinding> getAdditionalBindings(ExpressionTypechecker typechecker) {
    return meta instanceof UsingMeta ? ((UsingMeta) meta).getNewBindings(argument, typechecker) : Collections.emptyList();
  }

  public List<CoreBinding> getAllBindings(ExpressionTypechecker typechecker) {
    List<CoreBinding> list1 = getContextBindings(typechecker);
    List<CoreBinding> list2 = getAdditionalBindings(typechecker);
    if (!list1.isEmpty() && !list2.isEmpty()) {
      list1.addAll(list2);
      return list1;
    } else {
      return list2.isEmpty() ? list1 : list2;
    }
  }
}
