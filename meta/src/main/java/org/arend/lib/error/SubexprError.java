package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettifier.ExpressionPrettifier;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.jetbrains.annotations.Nullable;

import java.util.List;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class SubexprError extends TypecheckingError {
  private final ExpressionPrettifier prettifier;
  private final CoreExpression subexpr;
  private final CoreExpression subexprType;
  private final CoreExpression expr;

  public SubexprError(ExpressionPrettifier prettifier, List<Integer> occurrences, CoreExpression subexpr, CoreExpression subexprType, CoreExpression expr, @Nullable ConcreteSourceNode cause) {
    super("Cannot find subexpression" + (occurrences == null ? "" : " at " + occurrences.stream().map(x -> x + 1).toList()), cause);
    this.prettifier = prettifier;
    this.expr = expr;
    this.subexpr = subexpr;
    this.subexprType = subexprType;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    Doc expectedDoc = hang(text("Subexpression:"), subexprType == null ? termDoc(subexpr, prettifier, ppConfig) : hang(termDoc(subexpr, prettifier, ppConfig), hang(text(":"), termDoc(subexprType, prettifier, ppConfig))));
    return vList(
        expectedDoc,
        hang(text(expectedDoc.getHeight() == 1 ? "   Expression:" : "Expression:"), termDoc(expr, prettifier, ppConfig)));
  }

  @Override
  public boolean hasExpressions() {
    return true;
  }
}
