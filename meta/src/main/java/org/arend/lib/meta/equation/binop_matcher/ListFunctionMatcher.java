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
import java.util.Arrays;
import java.util.List;

public class ListFunctionMatcher implements FunctionMatcher {
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;
  private final StdExtension ext;

  public ListFunctionMatcher(ExpressionTypechecker typechecker, ConcreteFactory factory, StdExtension ext) {
    this.typechecker = typechecker;
    this.factory = factory;
    this.ext = ext;
  }

  @Override
  public List<CoreExpression> match(CoreExpression expr) {
    if (expr instanceof CoreFunCallExpression && ((CoreFunCallExpression) expr).getDefinition() == ext.append) {
      List<? extends CoreExpression> defCallArgs = ((CoreFunCallExpression) expr).getDefCallArguments();
      List<CoreExpression> args = new ArrayList<>(2);
      args.add(defCallArgs.get(1));
      args.add(defCallArgs.get(2));
      return args;
    } else if (expr instanceof CoreConCallExpression && ((CoreConCallExpression) expr).getDefinition() == ext.cons) {
      List<? extends CoreExpression> defCallArgs = ((CoreConCallExpression) expr).getDefCallArguments();
      CoreExpression tail = defCallArgs.get(1).normalize(NormalizationMode.WHNF);
      if (!(tail instanceof CoreConCallExpression && ((CoreConCallExpression) tail).getDefinition() == ext.nil)) {
        TypedExpression result = typechecker.typecheck(factory.app(factory.ref(ext.cons.getRef()), true, Arrays.asList(factory.core(defCallArgs.get(0).computeTyped()), factory.ref(ext.nil.getRef()))), null);
        if (result != null) {
          List<CoreExpression> args = new ArrayList<>(2);
          args.add(result.getExpression());
          args.add(tail);
          return args;
        }
      }
    }
    return null;
  }
}
