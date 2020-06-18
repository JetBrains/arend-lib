package org.arend.lib.context;

import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.typechecking.ExpressionTypechecker;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class HidingContext implements Context {
  private final Context context;
  private final Set<CoreBinding> hiding;

  private HidingContext(Context context, Set<CoreBinding> hiding) {
    this.context = context;
    this.hiding = hiding;
  }

  public static HidingContext make(Context context, Set<CoreBinding> hiding) {
    if (context instanceof HidingContext) {
      Set<CoreBinding> newSet = new HashSet<>(((HidingContext) context).hiding);
      newSet.addAll(hiding);
      return new HidingContext(((HidingContext) context).context, newSet);
    } else {
      return new HidingContext(context, hiding);
    }
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
