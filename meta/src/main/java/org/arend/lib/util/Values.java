package org.arend.lib.util;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.expr.UncheckedExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.typechecking.ExpressionTypechecker;

import java.util.ArrayList;
import java.util.List;

public class Values<E extends UncheckedExpression> {
  protected final ExpressionTypechecker typechecker;
  protected final ConcreteSourceNode marker;
  protected final List<E> values = new ArrayList<>();

  public Values(ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
    this.typechecker = typechecker;
    this.marker = marker;
  }

  public int addValue(E value) {
    int index = getIndex(value);
    if (index == -1) {
      values.add(value);
      return values.size() - 1;
    } else {
      return index;
    }
  }

  protected boolean matches(UncheckedExpression value, UncheckedExpression element) {
    return typechecker != null ? Utils.safeCompare(typechecker, value, element, CMP.EQ, marker, false, true, true) : value.compare(element, CMP.EQ);
  }

  public int getIndex(UncheckedExpression value) {
    for (int i = 0; i < values.size(); i++) {
      if (matches(value, values.get(i))) {
        return i;
      }
    }
    return -1;
  }

  public E getValue(int index) {
    return values.get(index);
  }

  public List<E> getValues() {
    return values;
  }
}
