package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.jetbrains.annotations.Nullable;

public class FieldNotPropError extends TypecheckingError {
  private final CoreClassField classField;

  public FieldNotPropError(CoreClassField classField, @Nullable ConcreteSourceNode cause) {
    super("", cause);
    this.classField = classField;
  }

  @Override
  public LineDoc getShortHeaderDoc(PrettyPrinterConfig ppConfig) {
    return DocFactory.hList(DocFactory.text("The type of "), DocFactory.refDoc(classField.getRef()), DocFactory.text(" must be in \\Prop"));
  }
}
