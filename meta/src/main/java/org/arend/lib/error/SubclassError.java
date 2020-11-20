package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.arend.ext.reference.ArendRef;
import org.jetbrains.annotations.Nullable;

public class SubclassError extends TypecheckingError {
  public final boolean isSubclass;
  public final ArendRef classRef;

  public SubclassError(boolean isSubclass, ArendRef classRef, @Nullable ConcreteSourceNode cause) {
    super("", cause);
    this.isSubclass = isSubclass;
    this.classRef = classRef;
  }

  @Override
  public LineDoc getShortHeaderDoc(PrettyPrinterConfig ppConfig) {
    return DocFactory.hList(DocFactory.text("Expected a " + (isSubclass ? "subclass" : "superclass") + " of "), DocFactory.refDoc(classRef));
  }
}
