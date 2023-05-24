package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.arend.ext.reference.MetaRef;
import org.jetbrains.annotations.Nullable;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class InternalMetaError extends TypecheckingError {
  private final MetaRef externalMeta;

  public InternalMetaError(MetaRef externalMeta, @Nullable ConcreteSourceNode cause) {
    super("", cause);
    this.externalMeta = externalMeta;
  }

  @Override
  public LineDoc getShortHeaderDoc(PrettyPrinterConfig ppConfig) {
    return hList(text("This meta is allowed only under '"), refDoc(externalMeta), text("' meta"));
  }
}
