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

import org.jetbrains.annotations.NotNull;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class RewriteMeta extends BaseMetaDefinition {
  private final StdExtension ext;
  private final Mode mode;

  public enum Mode { IMMEDIATE_FORWARD, IMMEDIATE_BACKWARDS, DEFERRED_BACKWARDS }

  public RewriteMeta(StdExtension ext, Mode mode) {
    this.ext = ext;
    this.mode = mode;
  }

  public RewriteMeta(StdExtension ext) {
    this(ext, Mode.DEFERRED_BACKWARDS);
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
    List<? extends ConcreteArgument> args = contextData.getArguments();
    int currentArg = 0;
    Set<Integer> occurrences;
    if (!args.isEmpty() && !args.get(0).isExplicit()) {
      occurrences = new HashSet<>();
      if (args.get(0) instanceof ConcreteTupleExpression) {
        for (ConcreteExpression expr : ((ConcreteTupleExpression) args.get(0)).getFields()) {
          getNumber(expr, occurrences, typechecker.getErrorReporter());
        }
      } else {
        getNumber(args.get(0).getExpression(), occurrences, typechecker.getErrorReporter());
      }
      currentArg++;
    } else {
      occurrences = null;
    }

    CoreExpression expectedType = contextData.getExpectedType() == null ? null : contextData.getExpectedType().getUnderlyingExpression();
    boolean isForward = mode == Mode.IMMEDIATE_FORWARD || expectedType == null || args.size() > currentArg + 2;
    if ((isForward || mode == Mode.IMMEDIATE_BACKWARDS) && !checkContextData(contextData, typechecker.getErrorReporter())) {
      return null;
    }

    ConcreteExpression arg0 = args.get(currentArg++).getExpression();
    CheckedExpression path = typechecker.typecheck(arg0);
    if (path == null) {
      return null;
    }
    CoreFunCallExpression eq = path.getType().toEquality();
    if (eq == null) {
      typechecker.getErrorReporter().report(new TypeMismatchError(DocFactory.text("_ = _"), path.getType(), arg0));
      return null;
    }

    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    ConcreteExpression transport = factory.ref(ext.transport.getRef(), refExpr.getPLevel(), refExpr.getHLevel());

    if (!isForward && mode == Mode.IMMEDIATE_BACKWARDS && expectedType instanceof CoreInferenceReferenceExpression) {
      CoreExpression right = eq.getDefCallArguments().get(2).getUnderlyingExpression();
      if (right instanceof CoreInferenceReferenceExpression && ((CoreInferenceReferenceExpression) right).getVariable() == ((CoreInferenceReferenceExpression) expectedType).getVariable()) {
        ArendRef ref = factory.local("T");
        return typechecker.typecheck(transport
          .app(factory.lam(Collections.singletonList(factory.param(ref)), factory.ref(ref)))
          .app(factory.core("transport (\\lam T => T) {!} _", path))
          .app(args.get(currentArg).getExpression()));
      }
      isForward = true;
    }

    CheckedExpression lastArg;
    CoreExpression value;
    CoreExpression type;
    if (isForward) {
      lastArg = typechecker.typecheck(args.get(currentArg++).getExpression());
      if (lastArg == null) {
        return null;
      }
      value = eq.getDefCallArguments().get(1);
      type = lastArg.getType();
    } else {
      lastArg = null;
      value = eq.getDefCallArguments().get(2);
      type = expectedType;
    }

    ArendRef ref = factory.local("x");
    return typechecker.typecheck(transport
      .app(factory.lam(Collections.singletonList(factory.param(ref)), factory.meta("transport (\\lam x => {!}) _ _", new MetaDefinition() {
        @Override
        public CheckedExpression invoke(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          CheckedExpression var = typechecker.typecheck(factory.ref(ref));
          assert var != null;
          final int[] num = { 0 };
          CoreExpression absExpr = type.recreate(expression -> {
            if (typechecker.compare(expression, value, CMP.EQ, refExpr)) {
              num[0]++;
              return occurrences == null || occurrences.contains(num[0]) ? var.getExpression() : null;
            } else {
              return null;
            }
          });
          if (absExpr == null) {
            typechecker.getErrorReporter().report(new TypecheckingError("Cannot substitute expression", contextData.getReferenceExpression()));
            return null;
          }
          return typechecker.check(absExpr, refExpr);
        }
      })))
      .app(factory.core("transport _ {!} _", path))
      .app(lastArg == null ? args.get(currentArg++).getExpression() : factory.core("transport _ _ {!}", lastArg))
      .app(args.subList(currentArg, args.size())));
  }
}
