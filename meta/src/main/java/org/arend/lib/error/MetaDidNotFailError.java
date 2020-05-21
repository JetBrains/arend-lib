package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.jetbrains.annotations.Nullable;

public class MetaDidNotFailError extends TypecheckingError {
  public final CoreExpression result;

  public MetaDidNotFailError(CoreExpression result, @Nullable ConcreteSourceNode cause) {
    super("Meta did not fail", cause);
    this.result = result;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    return DocFactory.hang(DocFactory.text("Result:"), DocFactory.termDoc(result, ppConfig));
  }
}
