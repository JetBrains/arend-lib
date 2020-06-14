package org.arend.lib.meta.closure;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.jetbrains.annotations.Nullable;

public interface BinaryRelationClosure<V> {
  void addRelation(V value1, V value2, ConcreteExpression proof);
  @Nullable ConcreteExpression checkRelation(V value1, V value2);
}
