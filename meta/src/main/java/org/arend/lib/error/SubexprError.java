package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.jetbrains.annotations.Nullable;

import java.util.List;
import java.util.stream.Collectors;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class SubexprError extends TypecheckingError {
  private final CoreExpression subexpr;
  private final CoreExpression subexprType;
  private final CoreExpression expr;

  public SubexprError(List<Integer> occurrences, CoreExpression subexpr, CoreExpression subexprType, CoreExpression expr, @Nullable ConcreteSourceNode cause) {
    super("Cannot find subexpression" + (occurrences == null ? "" : " at " + occurrences.stream().map(x -> x + 1).collect(Collectors.toList())), cause);
    this.expr = expr;
    this.subexpr = subexpr;
    this.subexprType = subexprType;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    Doc expectedDoc = hang(text("Subexpression:"), subexprType == null ? termDoc(subexpr, ppConfig) : hang(termDoc(subexpr, ppConfig), hang(text(":"), termDoc(subexprType, ppConfig))));
    return vList(
        expectedDoc,
        hang(text(expectedDoc.getHeight() == 1 ? "   Expression:" : "Expression:"), termDoc(expr, ppConfig)));
  }

  @Override
  public boolean hasExpressions() {
    return true;
  }
}
