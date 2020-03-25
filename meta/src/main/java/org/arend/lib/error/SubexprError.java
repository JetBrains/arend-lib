package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.jetbrains.annotations.Nullable;

import java.util.Set;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class SubexprError extends TypecheckingError {
  private final CoreExpression subexpr;
  private final CoreExpression expr;

  public SubexprError(Set<Integer> occurrences, CoreExpression subexpr, CoreExpression expr, @Nullable ConcreteSourceNode cause) {
    super("Cannot find subexpression" + (occurrences == null ? "" : " at " + occurrences), cause);
    this.expr = expr;
    this.subexpr = subexpr;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    Doc expectedDoc = hang(text("Subexpression:"), termDoc(subexpr, ppConfig));
    return vList(
        expectedDoc,
        hang(text(expectedDoc.getHeight() == 1 ? "   Expression:" : "Expression:"), termDoc(expr, ppConfig)));
  }

  @Override
  public boolean hasExpressions() {
    return true;
  }
}
