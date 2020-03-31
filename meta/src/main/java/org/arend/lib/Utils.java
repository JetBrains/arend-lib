package org.arend.lib;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteNumberExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;

public class Utils {
  public static int getNumber(ConcreteExpression expression, ErrorReporter errorReporter) {
    if (expression instanceof ConcreteNumberExpression) {
      return ((ConcreteNumberExpression) expression).getNumber().intValue();
    } else {
      errorReporter.report(new TypecheckingError("Expected a number", expression));
      return -1;
    }
  }
}
