package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.jetbrains.annotations.Nullable;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class TypecheckBuildError extends TypecheckingError {
  private final CoreExpression expression;

  private TypecheckBuildError(String message, CoreExpression expression, @Nullable ConcreteSourceNode cause) {
    super(message, cause);
    this.expression = expression;
  }

  public static void report(ErrorReporter errorReporter, CoreExpression expression, ConcreteSourceNode cause) {
    report(errorReporter, "Invalid expression", expression, cause);
  }

  public static void report(ErrorReporter errorReporter, String message, CoreExpression expression, ConcreteSourceNode cause) {
    if (!expression.isError()) {
      errorReporter.report(new TypecheckBuildError(message, expression, cause));
    }
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    return hang(text("Expression:"), termDoc(expression, ppConfig));
  }
}
