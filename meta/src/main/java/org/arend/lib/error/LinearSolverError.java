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
  private final Equation<CoreExpression> equation;
  private final List<? extends Equation<CoreExpression>> equations;

  public LinearSolverError(ExpressionPrettifier prettifier, Equation<CoreExpression> equation, List<? extends Equation<CoreExpression>> equations, @Nullable ConcreteSourceNode cause) {
    super(equation == null ? "Cannot infer a contradiction" : "Cannot solve the equation", cause);
    this.equation = equation;
    this.prettifier = prettifier;
    this.equations = equations;
  }

  private Doc getEquationDoc(Equation<CoreExpression> equation, PrettyPrinterConfig ppConfig) {
    String op = switch (equation.operation) {
      case LESS -> "<";
      case LESS_OR_EQUALS -> "<=";
      case EQUALS -> "=";
    };
    return hang(termDoc(equation.lhsTerm, prettifier, ppConfig), hang(text(op), termDoc(equation.rhsTerm, prettifier, ppConfig)));
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    if (equations.isEmpty() && equation == null) return nullDoc();
    List<Doc> docs = new ArrayList<>(equations.size());
    for (Equation<CoreExpression> equation : equations) {
      docs.add(getEquationDoc(equation, ppConfig));
    }
    Doc result = hang(text("Assumptions:"), vList(docs));
    return equation == null ? result : vList(hang(text("Equation:"), getEquationDoc(equation, ppConfig)), result);
  }

  @Override
  public boolean hasExpressions() {
    return !(equations.isEmpty() && equation == null);
  }
}
