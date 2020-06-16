package org.arend.lib.context;

import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.typechecking.ExpressionTypechecker;

import java.util.List;
import java.util.Set;

public class HidingContext implements Context {
  private final Context context;
  private final Set<CoreBinding> hiding;

  public HidingContext(Context context, Set<CoreBinding> hiding) {
    this.context = context;
    this.hiding = hiding;
  }

  @Override
  public List<CoreBinding> getContextBindings(ExpressionTypechecker typechecker) {
    List<CoreBinding> result = context.getContextBindings(typechecker);
    result.removeAll(hiding);
    return result;
  }

  @Override
  public List<CoreBinding> getAdditionalBindings(ExpressionTypechecker typechecker) {
    return context.getAdditionalBindings(typechecker);
  }
}
