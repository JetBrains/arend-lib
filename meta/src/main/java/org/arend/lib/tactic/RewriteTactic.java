package org.arend.lib.tactic;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypeMismatchError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;

import javax.annotation.Nonnull;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class RewriteTactic extends BaseMetaDefinition {
  private final StdExtension ext;

  public RewriteTactic(StdExtension ext) {
    this.ext = ext;
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
  public CheckedExpression invoke(@Nonnull ExpressionTypechecker typechecker, @Nonnull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    int argNum = 0;
    Set<Integer> occurrences;
    if (!args.get(0).isExplicit()) {
      occurrences = new HashSet<>();
      if (args.get(0) instanceof ConcreteTupleExpression) {
        for (ConcreteExpression expr : ((ConcreteTupleExpression) args.get(0)).getFields()) {
          getNumber(expr, occurrences, typechecker.getErrorReporter());
        }
      } else {
        getNumber(args.get(0).getExpression(), occurrences, typechecker.getErrorReporter());
      }
      argNum++;
    } else {
      occurrences = null;
    }

    ConcreteExpression arg0 = args.get(argNum).getExpression();
    CheckedExpression path = typechecker.typecheck(arg0);
    if (path == null) {
      return null;
    }
    CoreFunCallExpression eq = path.getType().toEquality();
    if (eq == null) {
      typechecker.getErrorReporter().report(new TypeMismatchError(DocFactory.text("_ = _"), path.getType(), arg0));
      return null;
    }

    CoreExpression right = eq.getDefCallArguments().get(2);
    CoreExpression type = contextData.getExpectedType();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    ArendRef ref = factory.local("x");
    return typechecker.typecheck(
      factory.ref(ext.transport.getRef(), refExpr.getPLevel(), refExpr.getHLevel())
        .app(factory.lam(Collections.singletonList(factory.param(ref)), factory.meta("transport (\\lam x => {!}) _ _", new MetaDefinition() {
          @Override
          public CheckedExpression invoke(@Nonnull ExpressionTypechecker typechecker, @Nonnull ContextData contextData) {
            CheckedExpression var = typechecker.typecheck(factory.ref(ref));
            assert var != null;
            final int[] num = { 0 };
            CoreExpression absExpr = type.recreate(expression -> {
              if (typechecker.compare(expression, right, CMP.EQ, refExpr)) {
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
        .app(args.get(argNum + 1).getExpression()));
  }
}
