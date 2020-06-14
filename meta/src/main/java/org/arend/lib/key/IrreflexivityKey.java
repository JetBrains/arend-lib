package org.arend.lib.key;

import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.serialization.ArendDeserializer;
import org.arend.ext.serialization.ArendSerializer;
import org.arend.ext.serialization.DeserializationException;
import org.arend.ext.serialization.SerializableKey;
import org.arend.ext.typechecking.DefinitionListener;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.ContradictionMeta;
import org.jetbrains.annotations.NotNull;

import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class IrreflexivityKey extends SerializableKey<CoreClassField> implements DefinitionListener {
  private final StdExtension ext;

  public IrreflexivityKey(@NotNull String name, StdExtension ext) {
    super(name);
    this.ext = ext;
  }

  @NotNull
  @Override
  public byte[] serialize(@NotNull ArendSerializer serializer, CoreClassField object) {
    return ByteBuffer.allocate(4).putInt(serializer.getDefIndex(object)).array();
  }

  @NotNull
  @Override
  public CoreClassField deserialize(@NotNull ArendDeserializer deserializer, @NotNull byte[] data) throws DeserializationException {
    if (data.length != 4) {
      throw new DeserializationException("Expected byte array of length 8");
    }

    return deserializer.getDefFromIndex(ByteBuffer.wrap(data).getInt(), CoreClassField.class);
  }

  @Override
  public void typechecked(@NotNull CoreDefinition definition) {
    if (!(definition instanceof CoreClassDefinition)) {
      return;
    }

    CoreClassDefinition classDef = (CoreClassDefinition) definition;
    if (!classDef.isSubClassOf(ext.equationMeta.BaseSet)) {
      return;
    }

    for (CoreClassField field : classDef.getPersonalFields()) {
      List<CoreParameter> parameters = new ArrayList<>();
      CoreExpression codomain = field.getResultType().getPiParameters(parameters);
      if (!(parameters.size() == 2 && ContradictionMeta.isEmpty(codomain))) {
        continue;
      }

      CoreExpression type1 = parameters.get(0).getTypeExpr();
      if (!(type1 instanceof CoreFieldCallExpression)) {
        continue;
      }

      CoreFieldCallExpression fieldCall1 = (CoreFieldCallExpression) type1;
      if (!(fieldCall1.getDefinition() == ext.equationMeta.carrier && fieldCall1.getArgument() instanceof CoreReferenceExpression && ((CoreReferenceExpression) fieldCall1.getArgument()).getBinding() == field.getThisParameter())) {
        continue;
      }

      CoreExpression type2 = parameters.get(1).getTypeExpr();
      if (!(type2 instanceof CoreAppExpression)) {
        continue;
      }

      CoreAppExpression app2 = (CoreAppExpression) type2;
      if (!(app2.getFunction() instanceof CoreAppExpression && app2.getArgument() instanceof CoreReferenceExpression && ((CoreReferenceExpression) app2.getArgument()).getBinding() == parameters.get(0).getBinding())) {
        continue;
      }

      CoreAppExpression app1 = (CoreAppExpression) app2.getFunction();
      if (!(app1.getFunction() instanceof CoreFieldCallExpression && app1.getArgument() instanceof CoreReferenceExpression && ((CoreReferenceExpression) app1.getArgument()).getBinding() == parameters.get(0).getBinding())) {
        continue;
      }

      CoreFieldCallExpression fieldCall2 = (CoreFieldCallExpression) app1.getFunction();
      if (!(fieldCall2.getArgument() instanceof CoreReferenceExpression && ((CoreReferenceExpression) fieldCall2.getArgument()).getBinding() == field.getThisParameter())) {
        continue;
      }

      Set<CoreBinding> bindings = new HashSet<>();
      bindings.add(field.getThisParameter().getBinding());
      bindings.add(parameters.get(0).getBinding());
      bindings.add(parameters.get(1).getBinding());
      if (codomain.findFreeBindings(bindings) != null) {
        continue;
      }

      fieldCall2.getDefinition().putUserData(this, field);
      break;
    }
  }
}
