package org.arend.lib.meta.pi_tree;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.lib.StdExtension;

import java.util.Arrays;

public class PathExpression {
  public final ConcreteExpression pathExpression;

  public PathExpression(ConcreteExpression pathExpression) {
    this.pathExpression = pathExpression;
  }

  protected ConcreteExpression applyAt(ConcreteExpression arg, ArendRef iRef, ConcreteFactory factory, StdExtension ext) {
    return factory.app(factory.ref(ext.prelude.getAtRef()), true, Arrays.asList(arg, factory.ref(iRef)));
  }

  public ConcreteExpression applyAt(ArendRef iRef, ConcreteFactory factory, StdExtension ext) {
    return applyAt(pathExpression, iRef, factory, ext);
  }
}
