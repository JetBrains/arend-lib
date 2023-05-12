package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.arend.ext.reference.ArendRef;
import org.jetbrains.annotations.Nullable;

public class UnknownReferenceError extends TypecheckingError {
  public final ArendRef reference;

  public UnknownReferenceError(ArendRef reference, @Nullable ConcreteSourceNode cause) {
    super("", cause);
    this.reference = reference;
  }

  @Override
  public LineDoc getShortHeaderDoc(PrettyPrinterConfig ppConfig) {
    return DocFactory.hList(DocFactory.text("Unknown reference '"), DocFactory.refDoc(reference), DocFactory.text("'"));
  }
}
