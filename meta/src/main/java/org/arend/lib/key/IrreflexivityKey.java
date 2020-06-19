package org.arend.lib.key;

import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.expr.*;
import org.arend.ext.typechecking.DefinitionListener;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.ContradictionMeta;
import org.jetbrains.annotations.NotNull;

import java.util.*;

public class IrreflexivityKey extends FieldKey implements DefinitionListener {
  public IrreflexivityKey(@NotNull String name, StdExtension ext) {
    super(name, ext);
  }

  @Override
  protected int getNumberOfParameters() {
    return 0;
  }

  @Override
  protected boolean checkField(CoreClassField field) {
    List<CoreParameter> parameters = new ArrayList<>();
    CoreExpression codomain = field.getResultType().getPiParameters(parameters);
    if (!(parameters.size() == 2 && ContradictionMeta.isEmpty(codomain) && isBaseSetCall(parameters.get(0).getTypeExpr(), field))) {
      return false;
    }

    CoreClassField relation = getFieldApplied(parameters.get(1).getTypeExpr(), parameters.get(0).getBinding(), parameters.get(0).getBinding(), field);
    if (relation == null) {
      return false;
    }

    Set<CoreBinding> bindings = new HashSet<>();
    bindings.add(field.getThisParameter().getBinding());
    bindings.add(parameters.get(0).getBinding());
    bindings.add(parameters.get(1).getBinding());
    if (codomain.findFreeBindings(bindings) != null) {
      return false;
    }

    putData(relation, field, Collections.emptyList());
    return true;
  }
}
