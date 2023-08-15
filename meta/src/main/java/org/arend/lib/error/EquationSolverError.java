package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.arend.lib.ring.Monomial;
import org.jetbrains.annotations.Nullable;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class EquationSolverError extends TypecheckingError {
  private static final String BASE_NAME = "v";
  public final List<Monomial> nf1;
  public final List<Monomial> nf2;
  public final List<CoreExpression> values;
  public final List<Assumption> assumptions;

  public static class Assumption {
    final CoreExpression expression;
    final CoreBinding binding;
    final boolean isBindingInverted;
    final List<Monomial> lhs;
    final List<Monomial> rhs;

    public Assumption(CoreExpression expression, CoreBinding binding, boolean isBindingInverted, List<Monomial> lhs, List<Monomial> rhs) {
      this.expression = expression;
      this.binding = binding;
      this.isBindingInverted = isBindingInverted;
      this.lhs = lhs;
      this.rhs = rhs;
    }
  }

  public EquationSolverError(String message, List<Monomial> nf1, List<Monomial> nf2, List<CoreExpression> values, List<Assumption> assumptions, @Nullable ConcreteSourceNode cause) {
    super(message, cause);
    this.nf1 = nf1;
    this.nf2 = nf2;
    this.values = values;
    this.assumptions = assumptions;
  }

  protected LineDoc nfToDoc(List<Monomial> nf) {
    if (nf.isEmpty()) {
      return text("0");
    }

    List<LineDoc> docs = new ArrayList<>(nf.size());
    for (Monomial m : nf) {
      List<LineDoc> mDocs = new ArrayList<>();
      for (Integer n : m.elements) {
        mDocs.add(text(BASE_NAME + n));
      }
      LineDoc mDoc = mDocs.isEmpty() ? text("1") : hSep(text(" * "), mDocs);
      docs.add(m.coefficient.equals(BigInteger.ONE) ? mDoc : mDocs.isEmpty() ? text(m.coefficient.toString()) : hList(text(m.coefficient + " * "), mDoc));
    }
    return hSep(text(" + "), docs);
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    LineDoc equationDoc = hList(text("Equation: "), nfToDoc(nf1), text(" = "), hList(nfToDoc(nf2)));

    Doc assumptionsDoc;
    if (!assumptions.isEmpty()) {
      List<Doc> docs = new ArrayList<>();
      for (Assumption assumption : assumptions) {
        docs.add(hang(assumption.expression != null ? termDoc(assumption.expression, ppConfig) : assumption.binding != null ? hList(assumption.isBindingInverted ? text("inv ") : empty(), text(assumption.binding.getName())) : nullDoc(), hList(text(": "), nfToDoc(assumption.lhs), text(" = "), nfToDoc(assumption.rhs))));
      }
      assumptionsDoc = hang(text("Assumptions:"), vList(docs));
    } else {
      assumptionsDoc = nullDoc();
    }

    Doc whereDoc;
    if (!values.isEmpty()) {
      List<Doc> whereDocs = new ArrayList<>();
      for (int i = 0; i < values.size(); i++) {
        whereDocs.add(hang(text(BASE_NAME + i + " ="), termDoc(values.get(i), ppConfig)));
      }
      whereDoc = hang(text("where"), vList(whereDocs));
    } else {
      whereDoc = nullDoc();
    }

    return vList(equationDoc, assumptionsDoc, whereDoc);
  }

  @Override
  public boolean hasExpressions() {
    return true;
  }
}
