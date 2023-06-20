package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.jetbrains.annotations.Nullable;

public class CustomTypecheckingError extends TypecheckingError {
  private final LineDoc headerDoc;
  private final Doc bodyDoc;

  public CustomTypecheckingError(LineDoc headerDoc, Doc bodyDoc, @Nullable ConcreteSourceNode cause) {
    super(Level.ERROR, "", cause);
    this.headerDoc = headerDoc;
    this.bodyDoc = bodyDoc;
  }

  @Override
  public LineDoc getShortHeaderDoc(PrettyPrinterConfig ppConfig) {
    return headerDoc;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    return bodyDoc;
  }
}
