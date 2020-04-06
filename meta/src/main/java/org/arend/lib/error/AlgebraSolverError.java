package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.arend.lib.meta.AlgebraSolverMeta;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class AlgebraSolverError extends TypecheckingError {
  private static final String BASE_NAME = "c";
  public final List<Integer> nf1;
  public final List<Integer> nf2;
  public final List<CoreExpression> values;
  public final List<? extends AlgebraSolverMeta.Rule> assumptions;
  public final List<AlgebraSolverMeta.Step> trace1;
  public final List<AlgebraSolverMeta.Step> trace2;

  public AlgebraSolverError(List<Integer> nf1, List<Integer> nf2, List<CoreExpression> values, List<? extends AlgebraSolverMeta.Rule> assumptions, List<AlgebraSolverMeta.Step> trace1, List<AlgebraSolverMeta.Step> trace2, @Nullable ConcreteSourceNode cause) {
    super("Cannot solve algebraic equation:", cause);
    this.nf1 = nf1;
    this.nf2 = nf2;
    this.values = values;
    this.assumptions = assumptions;
    this.trace1 = trace1;
    this.trace2 = trace2;
  }

  private LineDoc nfToDoc(List<Integer> nf) {
    List<LineDoc> docs = new ArrayList<>(nf.size());
    for (Integer i : nf) {
      docs.add(text(BASE_NAME + i));
    }
    return hSep(text(" * "), docs);
  }

  private Doc traceToDoc(String text, List<Integer> term, List<AlgebraSolverMeta.Step> trace) {
    if (trace.isEmpty()) {
      return nullDoc();
    }
    List<LineDoc> docs = new ArrayList<>(trace.size() + 1);
    docs.add(nfToDoc(term));
    for (AlgebraSolverMeta.Step step : trace) {
      term = step.apply(term);
      docs.add(nfToDoc(term));
    }
    return hList(text("Trace of " + text + ": "), hSep(text(" = "), docs));
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    LineDoc equationDoc = hList(nfToDoc(nf1), text(" = "), hList(nfToDoc(nf2)));

    Doc assumptionsDoc;
    if (!assumptions.isEmpty()) {
      List<Doc> docs = new ArrayList<>();
      for (AlgebraSolverMeta.Rule rule : assumptions) {
        docs.add(hang(rule.expression != null ? termDoc(rule.expression.getExpression(), ppConfig) : rule.binding != null ? hList(rule.direction == AlgebraSolverMeta.Direction.BACKWARD ? text("inv ") : empty(), text(rule.binding.getName())) : nullDoc(), hList(text(" : "), nfToDoc(rule.lhs), text(" = "), nfToDoc(rule.rhs))));
      }
      assumptionsDoc = hang(text("Assumptions:"), vList(docs));
    } else {
      assumptionsDoc = nullDoc();
    }

    Doc whereDoc;
    if (!values.isEmpty()) {
      List<Doc> whereDocs = new ArrayList<>();
      for (int i = 0; i < values.size(); i++) {
        whereDocs.add(hang(text(BASE_NAME + i + " = "), termDoc(values.get(i), ppConfig)));
      }
      whereDoc = hang(text("where"), vList(whereDocs));
    } else {
      whereDoc = nullDoc();
    }

    return vList(equationDoc, assumptionsDoc, whereDoc, traceToDoc("left hand side", nf1, trace1), traceToDoc("right hand side", nf2, trace2));
  }

  @Override
  public boolean hasExpressions() {
    return true;
  }
}
