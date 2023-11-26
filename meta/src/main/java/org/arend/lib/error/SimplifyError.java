package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.jetbrains.annotations.Nullable;

import java.util.List;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;
import static org.arend.ext.prettyprinting.doc.DocFactory.termDoc;

public class SimplifyError extends TypecheckingError {
  private final List<CoreExpression> subexprList;
  private final CoreExpression type;

  public SimplifyError(List<CoreExpression> subexprList, CoreExpression type, @Nullable ConcreteSourceNode cause) {
    super("Cannot simplify subexpressions", cause);
    this.subexprList = subexprList;
    this.type = type;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    return vList(
        hang(text("Subexpressions:"), hSep(text(", "), subexprList.stream().map(x -> termLine(x, ppConfig)).toList())),
        hang(text("Type:"), termDoc(type, ppConfig)));
  }

  @Override
  public boolean hasExpressions() {
    return true;
  }
}
