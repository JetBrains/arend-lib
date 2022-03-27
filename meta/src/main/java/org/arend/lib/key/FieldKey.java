package org.arend.lib.key;

import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.expr.CoreAppExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFieldCallExpression;
import org.arend.ext.core.expr.CoreReferenceExpression;
import org.arend.ext.serialization.ArendDeserializer;
import org.arend.ext.serialization.ArendSerializer;
import org.arend.ext.serialization.DeserializationException;
import org.arend.ext.serialization.SerializableKey;
import org.arend.ext.typechecking.DefinitionListener;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;

import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.List;

public abstract class FieldKey extends SerializableKey<FieldKey.Data> implements DefinitionListener {
  public static class Data {
    public final CoreClassField field;
    public final List<Boolean> parametersExplicitness;

    Data(CoreClassField field, List<Boolean> parametersExplicitness) {
      this.field = field;
      this.parametersExplicitness = parametersExplicitness;
    }
  }

  protected final StdExtension ext;

  protected FieldKey(@NotNull String name, StdExtension ext) {
    super(name);
    this.ext = ext;
  }

  @Override
  public byte @NotNull [] serialize(@NotNull ArendSerializer serializer, Data data) {
    ByteBuffer buffer = ByteBuffer.allocate(4 + data.parametersExplicitness.size());
    for (Boolean explicitness : data.parametersExplicitness) {
      buffer.put((byte) (explicitness ? 1 : 0));
    }
    buffer.putInt(serializer.getDefIndex(data.field));
    return buffer.array();
  }

  protected abstract int getNumberOfParameters();

  @NotNull
  @Override
  public Data deserialize(@NotNull ArendDeserializer deserializer, byte @NotNull [] data) throws DeserializationException {
    int length = 4 + getNumberOfParameters();
    if (data.length != length) {
      throw new DeserializationException("Expected byte array of length " + length);
    }

    ByteBuffer buffer = ByteBuffer.wrap(data);
    List<Boolean> explicitness = new ArrayList<>(data.length - 4);
    for (int i = 0; i < data.length - 4; i++) {
      byte b = buffer.get();
      if (b != 0 && b != 1) {
        throw new DeserializationException("Expected a boolean");
      }
      explicitness.add(b == 1);
    }
    return new Data(deserializer.getDefFromIndex(buffer.getInt(), CoreClassField.class), explicitness);
  }

  protected void putData(CoreClassField relation, CoreClassField field, List<CoreParameter> parameters) {
    List<Boolean> explicitness = new ArrayList<>(parameters.size());
    for (CoreParameter parameter : parameters) {
      explicitness.add(parameter.isExplicit());
    }
    relation.putUserData(this, new Data(field, explicitness));
  }

  protected abstract boolean checkField(CoreClassField field);

  protected boolean isBaseSetCall(CoreExpression type, CoreClassField field) {
    if (!(type instanceof CoreFieldCallExpression)) {
      return false;
    }

    CoreFieldCallExpression fieldCall = (CoreFieldCallExpression) type;
    return fieldCall.getDefinition() == ext.carrier && fieldCall.getArgument() instanceof CoreReferenceExpression && ((CoreReferenceExpression) fieldCall.getArgument()).getBinding() == field.getThisParameter();
  }

  protected CoreClassField getFieldApplied(CoreExpression type, CoreBinding var1, CoreBinding var2, CoreClassField field) {
    if (!(type instanceof CoreAppExpression)) {
      return null;
    }

    CoreAppExpression app2 = (CoreAppExpression) type;
    if (!(app2.getFunction() instanceof CoreAppExpression && app2.getArgument() instanceof CoreReferenceExpression && ((CoreReferenceExpression) app2.getArgument()).getBinding() == var2)) {
      return null;
    }

    CoreAppExpression app1 = (CoreAppExpression) app2.getFunction();
    if (!(app1.getFunction() instanceof CoreFieldCallExpression && app1.getArgument() instanceof CoreReferenceExpression && ((CoreReferenceExpression) app1.getArgument()).getBinding() == var1)) {
      return null;
    }

    CoreFieldCallExpression fieldCall = (CoreFieldCallExpression) app1.getFunction();
    if (!(fieldCall.getArgument() instanceof CoreReferenceExpression && ((CoreReferenceExpression) fieldCall.getArgument()).getBinding() == field.getThisParameter())) {
      return null;
    }

    return fieldCall.getDefinition();
  }

  @Override
  public void typechecked(@NotNull CoreDefinition definition) {
    if (!(definition instanceof CoreClassDefinition)) {
      return;
    }

    CoreClassDefinition classDef = (CoreClassDefinition) definition;
    if (ext.BaseSet == null || !classDef.isSubClassOf(ext.BaseSet)) {
      return;
    }

    for (CoreClassField field : classDef.getPersonalFields()) {
      if (checkField(field)) {
        break;
      }
    }
  }
}
