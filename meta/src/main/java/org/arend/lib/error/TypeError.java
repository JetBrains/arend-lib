package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.UncheckedExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettifier.ExpressionPrettifier;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.jetbrains.annotations.Nullable;

public class TypeError extends TypecheckingError {
  public final ExpressionPrettifier prettifier;
  public final UncheckedExpression type;

  public TypeError(ExpressionPrettifier prettifier, String message, UncheckedExpression type, @Nullable ConcreteSourceNode cause) {
    super(message, cause);
    this.prettifier = prettifier;
    this.type = type;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    return DocFactory.hang(DocFactory.text("Type:"), DocFactory.termDoc(type, prettifier, ppConfig));
  }

  @Override
  public boolean hasExpressions() {
    return true;
  }
}
