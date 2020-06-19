package org.arend.lib.key;

import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;

public class ReflexivityKey extends FieldKey {
  public ReflexivityKey(@NotNull String name, StdExtension ext) {
    super(name, ext);
  }

  @Override
  protected int getNumberOfParameters() {
    return 1;
  }

  @Override
  protected boolean checkField(CoreClassField field) {
    List<CoreParameter> parameters = new ArrayList<>();
    CoreExpression codomain = field.getResultType().getPiParameters(parameters);
    if (!(parameters.size() == 1 && isBaseSetCall(parameters.get(0).getTypeExpr(), field))) {
      return false;
    }

    CoreClassField relation = getFieldApplied(codomain, parameters.get(0).getBinding(), parameters.get(0).getBinding(), field);
    if (relation == null) {
      return false;
    }

    putData(relation, field, parameters);
    return true;
  }
}
