package org.arend.lib.meta.monad;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.reference.ArendRef;
import org.arend.lib.StdExtension;

import java.util.Collections;

public class RunMeta extends BaseMonadMeta {
  public RunMeta(StdExtension ext) {
    super(ext);
  }

  @Override
  ConcreteExpression combine(ConcreteExpression expr1, ConcreteExpression expr2, ConcreteFactory factory) {
    return factory.app(expr1, true, Collections.singletonList(expr2));
  }

  @Override
  ConcreteExpression combine(ConcreteExpression expr1, ArendRef ref, ConcreteExpression expr2, ConcreteFactory factory) {
    return factory.app(expr1, true, factory.lam(Collections.singletonList(factory.param(ref)), expr2));
  }
}