package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.util.Maybe;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;
import java.util.List;

public interface EquationSolver {
  boolean isApplicable(CoreExpression type);
  CoreExpression getValuesType(); // the type of left and right hand sides
  CoreExpression getLeftValue();  // the left hand side of the equation
  CoreExpression getRightValue(); // the right hand side of the equation

  @Nullable Maybe<CoreExpression> getEqType(@Nullable TypedExpression leftExpr, @Nullable TypedExpression rightExpr); // the type of equality between two expressions
  TypedExpression getTrivialResult(TypedExpression expression); // reflexivity, trivial path, etc
  ConcreteExpression combineResults(ConcreteExpression expr1, ConcreteExpression expr2); // transitivity, concatenation, etc

  boolean isHint(ConcreteExpression expression);
  boolean initializeSolver();
  ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter);
  SubexprOccurrences matchSubexpr(@NotNull TypedExpression subExpr, @NotNull TypedExpression expr, @NotNull ErrorReporter errorReporter, List<Integer> occurrences);
  TypedExpression finalize(ConcreteExpression result);

  class SubexprOccurrences {
    public ArendRef occurrenceVar = null;
    public ConcreteExpression exprWithOccurrences = null;
    // Proof of expr = exprWithOccurrence.substitute(occurrenceVar -> subExpr);
    public ConcreteExpression equalityProof = null;
    // Number of occurrences of subExpr in exprWithOccurrences to the right of the last occurrence
    public int numOccurrencesSkipped = 0;
    public int numOccurrences = 0;
    // Temporary hack
    public boolean subExprMissed = true;

    public SubexprOccurrences() {
    }

    public SubexprOccurrences(ArendRef occurrenceVar, ConcreteExpression exprWithOccurrences, ConcreteExpression equalityProof, int numOccurrences, int numOccurrencesSkipped) {
      this.occurrenceVar = occurrenceVar;
      this.exprWithOccurrences = exprWithOccurrences;
      this.equalityProof = equalityProof;
      this.numOccurrencesSkipped = numOccurrencesSkipped;
      this.numOccurrences = numOccurrences;
    }

    public static SubexprOccurrences simpleSingletonOccur(ConcreteFactory factory, CoreExpression subExprType, ConcreteExpression eqProof) {
      SubexprOccurrences result = new SubexprOccurrences();

      result.occurrenceVar = factory.local("occurVar");
      result.exprWithOccurrences = factory.ref(result.occurrenceVar);
      result.wrapExprWithOccurrences(factory.core(subExprType.computeTyped()), factory);
      result.equalityProof = eqProof;
      result.numOccurrences = 1;
      result.numOccurrencesSkipped = 0;
      return result;
    }

    public boolean doesExist() { return occurrenceVar != null; }

    public void wrapExprWithOccurrences(ConcreteExpression type, ConcreteFactory factory) {
      exprWithOccurrences = factory.lam(Collections.singletonList(factory.param(Collections.singletonList(occurrenceVar), type)), exprWithOccurrences);
    }
  }
}
