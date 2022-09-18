package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.lib.meta.linear.Equation;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class LinearSolverError extends TypecheckingError {
  private final List<? extends Equation<CoreExpression>> equations;

  public LinearSolverError(boolean isContradiction, List<? extends Equation<CoreExpression>> equations, @Nullable ConcreteSourceNode cause) {
    super(isContradiction ? "Cannot infer a contradiction" : "Cannot solve the equation", cause);
    this.equations = equations;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    List<Doc> docs = new ArrayList<>(equations.size());
    for (Equation<CoreExpression> equation : equations) {
      String op;
      switch (equation.operation) {
        case LESS: op = "<";break;
        case LESS_OR_EQUALS: op = "<="; break;
        case EQUALS: op = "="; break;
        default: throw new IllegalStateException();
      }
      docs.add(hang(termDoc(equation.lhsTerm, ppConfig), hang(text(op), termDoc(equation.rhsTerm, ppConfig))));
    }
    return hang(text("Assumptions:"), vList(docs));
  }
}
