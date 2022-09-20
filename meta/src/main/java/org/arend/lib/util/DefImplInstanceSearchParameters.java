package org.arend.lib.util;

import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.instance.InstanceSearchParameters;
import org.jetbrains.annotations.NotNull;

import java.util.Collections;
import java.util.List;

public abstract class DefImplInstanceSearchParameters implements InstanceSearchParameters {
  private final CoreDefinition definition;
  private List<CoreClassField> relationFields = Collections.emptyList();
  private CoreClassField relationField;

  protected DefImplInstanceSearchParameters(CoreDefinition definition) {
    this.definition = definition;
  }

  protected abstract List<CoreClassField> getRelationFields(CoreClassDefinition classDef);

  public CoreClassField getRelationField() {
    return relationField;
  }

  @Override
  public boolean testClass(@NotNull CoreClassDefinition classDefinition) {
    relationFields = getRelationFields(classDefinition);
    return !relationFields.isEmpty();
  }

  @Override
  public boolean testGlobalInstance(@NotNull CoreFunctionDefinition instance) {
    if (!(instance.getResultType() instanceof CoreClassCallExpression)) {
      return false;
    }

    for (CoreClassField relationField : relationFields) {
      CoreAbsExpression absImpl = ((CoreClassCallExpression) instance.getResultType()).getAbsImplementation(relationField);
      if (absImpl == null) {
        continue;
      }
      CoreExpression impl = absImpl.getExpression();
      if (!(impl instanceof CoreLamExpression)) {
        continue;
      }

      CoreParameter param1 = ((CoreLamExpression) impl).getParameters();
      CoreParameter param2 = param1.getNext();
      CoreExpression body = ((CoreLamExpression) impl).getBody();
      if (!param2.hasNext()) {
        if (!(body instanceof CoreLamExpression)) {
          continue;
        }
        param2 = ((CoreLamExpression) body).getParameters();
        body = ((CoreLamExpression) body).getBody();
      }
      if (param2.getNext().hasNext()) {
        continue;
      }

      if (!(body instanceof CoreDefCallExpression)) {
        continue;
      }
      CoreDefCallExpression defCall = (CoreDefCallExpression) body;
      var args = defCall.getDefCallArguments();
      if (defCall.getDefinition() == definition && args.size() >= 2 && args.get(args.size() - 2) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(args.size() - 2)).getBinding() == param1.getBinding() && args.get(args.size() - 1) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(args.size() - 1)).getBinding() == param2.getBinding()) {
        this.relationField = relationField;
        return true;
      }
    }

    return false;
  }
}
