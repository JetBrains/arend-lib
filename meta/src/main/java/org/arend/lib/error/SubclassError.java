package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.arend.ext.reference.ArendRef;
import org.jetbrains.annotations.Nullable;

public class SubclassError extends TypecheckingError {
  public final ArendRef classRef;

  public SubclassError(ArendRef classRef, @Nullable ConcreteSourceNode cause) {
    super("", cause);
    this.classRef = classRef;
  }

  @Override
  public LineDoc getShortHeaderDoc(PrettyPrinterConfig ppConfig) {
    return DocFactory.hList(DocFactory.text("Expected a subclass of "), DocFactory.refDoc(classRef));
  }
}
