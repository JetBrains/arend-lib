package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.arend.lib.meta.equation.MonoidSolver;
import org.arend.lib.ring.Monomial;
import org.jetbrains.annotations.Nullable;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;
import static org.arend.ext.prettyprinting.doc.DocFactory.nullDoc;

public class MonoidSolverError extends EquationSolverError {
  private final boolean isMultiplicative;
  private final List<Integer> monoidNF1;
  private final List<Integer> monoidNF2;
  public final List<MonoidSolver.Step> trace1;
  public final List<MonoidSolver.Step> trace2;

  public MonoidSolverError(boolean isMultiplicative, List<Integer> nf1, List<Integer> nf2, List<CoreExpression> values, List<? extends MonoidSolver.Rule> rules, List<MonoidSolver.Step> trace1, List<MonoidSolver.Step> trace2, @Nullable ConcreteSourceNode cause) {
    super("Monoid solver failed", toMonomials(nf1, isMultiplicative), toMonomials(nf2, isMultiplicative), values, rulesToAssumptions(rules, isMultiplicative), cause);
    this.isMultiplicative = isMultiplicative;
    monoidNF1 = nf1;
    monoidNF2 = nf2;
    this.trace1 = trace1;
    this.trace2 = trace2;
  }

  private static List<Monomial> toMonomials(List<Integer> nf, boolean isMultiplicative) {
    if (isMultiplicative) {
      return Collections.singletonList(new Monomial(BigInteger.ONE, nf));
    }
    List<Monomial> result = new ArrayList<>(nf.size());
    for (Integer n : nf) {
      result.add(new Monomial(BigInteger.ONE, Collections.singletonList(n)));
    }
    return result;
  }

  private static List<Assumption> rulesToAssumptions(List<? extends MonoidSolver.Rule> rules, boolean isMultiplicative) {
    List<Assumption> result = new ArrayList<>(rules.size());
    for (MonoidSolver.Rule rule : rules) {
      result.add(new Assumption(rule.expression == null ? null : rule.expression.getExpression(), rule.binding, rule.direction == MonoidSolver.Direction.BACKWARD, toMonomials(rule.lhs, isMultiplicative), toMonomials(rule.rhs, isMultiplicative)));
    }
    return result;
  }

  private Doc traceToDoc(String text, List<Integer> term, List<MonoidSolver.Step> trace) {
    if (trace.isEmpty()) {
      return nullDoc();
    }
    List<LineDoc> docs = new ArrayList<>(trace.size() + 1);
    docs.add(nfToDoc(toMonomials(term, isMultiplicative)));
    for (MonoidSolver.Step step : trace) {
      term = step.apply(term);
      docs.add(nfToDoc(toMonomials(term, isMultiplicative)));
    }
    return hList(text("Trace of " + text + ": "), hSep(text(" = "), docs));
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    Doc result = super.getBodyDoc(ppConfig);
    return vList(result, traceToDoc("left hand side", monoidNF1, trace1), traceToDoc("right hand side", monoidNF2, trace2));
  }
}
