package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettifier.ExpressionPrettifier;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.lib.meta.linear.Equation;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class LinearSolverError extends TypecheckingError {
  private final ExpressionPrettifier prettifier;
  private final List<? extends Equation<CoreExpression>> equations;

  public LinearSolverError(ExpressionPrettifier prettifier, boolean isContradiction, List<? extends Equation<CoreExpression>> equations, @Nullable ConcreteSourceNode cause) {
    super(isContradiction ? "Cannot infer a contradiction" : "Cannot solve the equation", cause);
    this.prettifier = prettifier;
    this.equations = equations;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    if (equations.isEmpty()) return nullDoc();
    List<Doc> docs = new ArrayList<>(equations.size());
    for (Equation<CoreExpression> equation : equations) {
      String op = switch (equation.operation) {
        case LESS -> "<";
        case LESS_OR_EQUALS -> "<=";
        case EQUALS -> "=";
      };
      docs.add(hang(termDoc(equation.lhsTerm, prettifier, ppConfig), hang(text(op), termDoc(equation.rhsTerm, prettifier, ppConfig))));
    }
    return hang(text("Assumptions:"), vList(docs));
  }
}
