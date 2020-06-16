package org.arend.lib.context;

import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.typechecking.ExpressionTypechecker;

import java.util.Collections;
import java.util.List;

public interface Context {
  Context TRIVIAL = new Context() {};

  default List<CoreBinding> getContextBindings(ExpressionTypechecker typechecker) {
    return typechecker.getFreeBindingsList();
  }

  default List<CoreBinding> getAdditionalBindings(ExpressionTypechecker typechecker) {
    return Collections.emptyList();
  }

  default List<CoreBinding> getAllBindings(ExpressionTypechecker typechecker) {
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
