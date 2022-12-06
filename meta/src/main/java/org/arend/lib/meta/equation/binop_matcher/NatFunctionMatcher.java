package org.arend.lib.meta.equation.binop_matcher;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;

import java.util.ArrayList;
import java.util.List;

public class NatFunctionMatcher implements FunctionMatcher {
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;
  private final StdExtension ext;

  public NatFunctionMatcher(ExpressionTypechecker typechecker, ConcreteFactory factory, StdExtension ext) {
    this.typechecker = typechecker;
    this.factory = factory;
    this.ext = ext;
  }

  @Override
  public List<CoreExpression> match(CoreExpression expr) {
    if (expr instanceof CoreFunCallExpression && ((CoreFunCallExpression) expr).getDefinition() == ext.prelude.getPlus()) {
      List<? extends CoreExpression> defCallArgs = ((CoreFunCallExpression) expr).getDefCallArguments();
      List<CoreExpression> args = new ArrayList<>(2);
      args.add(defCallArgs.get(0));
      args.add(defCallArgs.get(1));
      return args;
    } else if (expr instanceof CoreConCallExpression && ((CoreConCallExpression) expr).getDefinition() == ext.prelude.getSuc()) {
      TypedExpression result = typechecker.typecheck(factory.number(1), null);
      if (result == null) return null;
      List<CoreExpression> args = new ArrayList<>(2);
      args.add(((CoreConCallExpression) expr).getDefCallArguments().get(0).normalize(NormalizationMode.WHNF));
      args.add(result.getExpression());
      return args;
    }
    return null;
  }
}
