package org.arend.lib.meta.monad;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.lib.StdExtension;

import java.util.Collections;

public class DoMeta extends BaseMonadMeta {
  public DoMeta(StdExtension ext) {
    super(ext);
  }

  @Override
  ConcreteExpression combine(ConcreteExpression expr1, ConcreteExpression expr2, ConcreteFactory factory) {
    return combine(expr1, null, expr2, factory);
  }

  @Override
  ConcreteExpression combine(ConcreteExpression expr1, ArendRef ref, ConcreteExpression expr2, ConcreteFactory factory) {
    return factory.app(factory.ref(ext.ioBind), true, expr1, factory.lam(Collections.singletonList(factory.param(ref)), expr2));
  }
}
