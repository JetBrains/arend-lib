package org.arend.lib.meta.equation.term;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;
import org.arend.lib.util.Values;

import java.util.List;
import java.util.function.Function;

public interface CompiledTerm {
  static CompiledTerm compile(CoreExpression expression, List<FunctionMatcher> matchers, Values<CoreExpression> values) {
    for (var matcher : matchers) {
      List<CoreExpression> args = matcher.match(expression);
      if (args != null) {
        var term = new CompositeTerm();
        term.matcher = matcher;
        for (var arg : args) {
          var subterm = compile(arg, matchers, values);
          if (subterm == null) return null;
          term.subterms.add(subterm);
        }
        return term;
      }
    }
    int index = values.addValue(expression);
    return new VarTerm(index);
  }

  static ConcreteExpression termToConcrete(CompiledTerm term, Function<FunctionMatcher, ConcreteExpression> concreteOperator, Function<Integer, ConcreteExpression> concreteVar, ConcreteFactory factory) {
    if (term instanceof CompositeTerm compositeTerm) {
      var operator = concreteOperator.apply(compositeTerm.matcher);
      if (operator == null) return null;
      var concreteExprBuilder = factory.appBuilder(operator);
      for (var subterm : compositeTerm.subterms) {
        var concreteSubterm = termToConcrete(subterm, concreteOperator, concreteVar, factory);
        if (concreteSubterm == null) return null;
        concreteExprBuilder.app(concreteSubterm);
      }
      return concreteExprBuilder.build();
    } else if (term instanceof VarTerm varTerm) {
      return concreteVar.apply(varTerm.index);
    }
    return null;
  }
}

