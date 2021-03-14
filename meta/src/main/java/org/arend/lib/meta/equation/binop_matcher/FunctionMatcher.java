package org.arend.lib.meta.equation.binop_matcher;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.expr.*;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;

import java.util.List;

public interface FunctionMatcher {
  List<CoreExpression> match(CoreExpression expr);

  static FunctionMatcher makeFieldMatcher(CoreClassCallExpression classCall, TypedExpression instance, CoreClassField field, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteSourceNode marker, StdExtension ext, int numberOfArguments) {
    CoreExpression expr = classCall.getImplementation(field, instance);
    if (numberOfArguments == 0 && expr != null) {
      return new ExpressionFunctionMatcher(typechecker, factory, marker, expr.computeTyped(), null, 0);
    }
    if (!(expr instanceof CoreLamExpression)) {
      return new DefinitionFunctionMatcher(field, numberOfArguments);
    }

    CoreExpression body = ((CoreLamExpression) expr).getBody();
    CoreParameter param1 = ((CoreLamExpression) expr).getParameters();
    CoreParameter param2 = param1.getNext();
    if (!param2.hasNext() && body instanceof CoreLamExpression) {
      param2 = ((CoreLamExpression) body).getParameters();
      body = ((CoreLamExpression) body).getBody();
    }
    if (param2.hasNext() && !param2.getNext().hasNext() && body instanceof CoreFunCallExpression) {
      CoreFunCallExpression funCall = (CoreFunCallExpression) body;
      if (funCall.getDefinition() == ext.append) {
        List<? extends CoreExpression> args = funCall.getDefCallArguments();
        if (args.get(1) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(1)).getBinding() == param1.getBinding() && args.get(2) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(2)).getBinding() == param2.getBinding()) {
          return new ListFunctionMatcher(typechecker, factory, ext);
        }
      } else if (funCall.getDefinition() == ext.prelude.getPlus()) {
        List<? extends CoreExpression> args = funCall.getDefCallArguments();
        if (args.get(0) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(0)).getBinding() == param1.getBinding() && args.get(1) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(1)).getBinding() == param2.getBinding()) {
          return new NatFunctionMatcher(typechecker, factory, ext);
        }
      }
    }
    return new ExpressionFunctionMatcher(typechecker, factory, marker, expr.computeTyped(), ((CoreLamExpression) expr).getParameters().getTypeExpr(), numberOfArguments);
  }
}
