package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.expr.CoreInferenceReferenceExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypeMismatchError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;

import org.arend.lib.error.SubexprError;
import org.jetbrains.annotations.NotNull;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class RewriteMeta extends BaseMetaDefinition {
  private final StdExtension ext;
  private final boolean isForward;
  private final boolean isInverse;

  public RewriteMeta(StdExtension ext, boolean isForward, boolean isInverse) {
    this.ext = ext;
    this.isForward = isForward;
    this.isInverse = isInverse;
  }

  @Override
  protected boolean[] argumentExplicitness() {
    return new boolean[] { false, true, true };
  }

  private void getNumber(ConcreteExpression expression, Set<Integer> result, ErrorReporter errorReporter) {
    if (expression instanceof ConcreteNumberExpression) {
      result.add(((ConcreteNumberExpression) expression).getNumber().intValue());
    } else {
      errorReporter.report(new TypecheckingError("Expected a number", expression));
    }
  }

  @Override
  public CheckedExpression invoke(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    List<? extends ConcreteArgument> args = contextData.getArguments();
    int currentArg = 0;
    Set<Integer> occurrences;
    if (!args.isEmpty() && !args.get(0).isExplicit()) {
      occurrences = new HashSet<>();
      if (args.get(0) instanceof ConcreteTupleExpression) {
        for (ConcreteExpression expr : ((ConcreteTupleExpression) args.get(0)).getFields()) {
          getNumber(expr, occurrences, errorReporter);
        }
      } else {
        getNumber(args.get(0).getExpression(), occurrences, errorReporter);
      }
      currentArg++;
    } else {
      occurrences = null;
    }

    CoreExpression expectedType = contextData.getExpectedType() == null ? null : contextData.getExpectedType().getUnderlyingExpression();
    boolean isForward = this.isForward || expectedType == null || args.size() > currentArg + 2;

    ConcreteExpression arg0 = args.get(currentArg++).getExpression();
    CheckedExpression path = typechecker.typecheck(arg0, null);
    if (path == null) {
      return null;
    }
    CoreFunCallExpression eq = path.getType().toEquality();
    if (eq == null) {
      errorReporter.report(new TypeMismatchError(DocFactory.text("_ = _"), path.getType(), arg0));
      return null;
    }

    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    ConcreteExpression transport = factory.ref((isInverse ? ext.transportInv : ext.transport).getRef(), refExpr.getPLevel(), refExpr.getHLevel());
    CoreExpression value = eq.getDefCallArguments().get(isInverse == isForward ? 2 : 1);

    if (!isForward && expectedType instanceof CoreInferenceReferenceExpression) {
      CoreExpression var = value.getUnderlyingExpression();
      if (var instanceof CoreInferenceReferenceExpression && ((CoreInferenceReferenceExpression) var).getVariable() == ((CoreInferenceReferenceExpression) expectedType).getVariable()) {
        if (!(occurrences == null || occurrences.isEmpty() || occurrences.size() == 1 && occurrences.contains(1))) {
          occurrences.remove(1);
          errorReporter.report(new SubexprError(occurrences, var, expectedType, refExpr));
          return null;
        }
        ArendRef ref = factory.local("T");
        return typechecker.typecheck(transport
          .app(factory.lam(Collections.singletonList(factory.param(ref)), factory.ref(ref)))
          .app(factory.core("transport (\\lam T => T) {!} _", path))
          .app(args.get(currentArg).getExpression()), null);
      }
      isForward = true;
    }

    CheckedExpression lastArg;
    CoreExpression type;
    if (isForward) {
      lastArg = typechecker.typecheck(args.get(currentArg++).getExpression(), null);
      if (lastArg == null) {
        return null;
      }
      type = lastArg.getType();
    } else {
      lastArg = null;
      type = expectedType;
    }

    ArendRef ref = factory.local("x");
    return typechecker.typecheck(transport
      .app(factory.lam(Collections.singletonList(factory.param(ref)), factory.meta("transport (\\lam x => {!}) _ _", new MetaDefinition() {
        @Override
        public CheckedExpression invoke(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          CheckedExpression var = typechecker.typecheck(factory.ref(ref), null);
          assert var != null;
          final int[] num = { 0 };
          CoreExpression absExpr = type.replaceSubexpressions(expression -> {
            if (typechecker.compare(expression, value, CMP.EQ, refExpr, false, true)) {
              num[0]++;
              if (occurrences == null || occurrences.contains(num[0])) {
                return var.getExpression();
              }
            }
            return null;
          });
          if (absExpr == null) {
            errorReporter.report(new TypecheckingError("Cannot substitute expression", refExpr));
            return null;
          }
          if (occurrences != null && num[0] > 0) {
            occurrences.removeIf(i -> i <= num[0]);
          }
          if (num[0] == 0 || occurrences != null && !occurrences.isEmpty()) {
            errorReporter.report(new SubexprError(occurrences, value, type, refExpr));
            return null;
          }
          return typechecker.check(absExpr, null, refExpr);
        }
      })))
      .app(factory.core("transport _ {!} _", path))
      .app(lastArg == null ? args.get(currentArg++).getExpression() : factory.core("transport _ _ {!}", lastArg))
      .app(args.subList(currentArg, args.size())), null);
  }
}
