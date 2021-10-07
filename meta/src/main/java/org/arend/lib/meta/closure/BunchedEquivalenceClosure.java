package org.arend.lib.meta.closure;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.util.Pair;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class BunchedEquivalenceClosure<V> extends EquivalenceClosure<V> {
  private final Map<V, V> representatives = new HashMap<>();
  private final Map<V, Pair<V, ConcreteExpression>> pathToRepr = new HashMap<>();

  public BunchedEquivalenceClosure(ConcreteExpression refl, ConcreteExpression sym, ConcreteExpression trans, ConcreteFactory factory) {
    super(refl, sym, trans, factory);
    assert sym != null;
  }

  @Override
  public void addRelation(V value1, V value2, ConcreteExpression proof) {
    representatives.clear();
    super.addRelation(value1, value2, proof);
  }

  private boolean setRepresentative(V value, V representative) {
    if (representatives.putIfAbsent(value, representative) != null) {
      return false;
    }

    List<Pair<V, ConcreteExpression>> list = graph.get(value);
    if (list == null) {
      return true;
    }

    for (Pair<V, ConcreteExpression> pair : list) {
      if (setRepresentative(pair.proj1, representative)) {
        pathToRepr.putIfAbsent(pair.proj1, new Pair<>(value, pair.proj2));
      }
    }

    return true;
  }

  private List<ConcreteExpression> computePathToRepr(V value, List<ConcreteExpression> result) {
    Pair<V, ConcreteExpression> pair = pathToRepr.get(value);
    if (pair == null) {
      return result;
    }

    result.add(pair.proj2);
    return computePathToRepr(pair.proj1, result);
  }

  private void compute() {
    if (representatives.isEmpty()) {
      pathToRepr.clear();
      for (V value : graph.keySet()) {
        setRepresentative(value, value);
      }
    }
  }

  public boolean areRelated(V value1, V value2) {
    if (value1.equals(value2)) {
      return true;
    }

    compute();

    var repr1 = representatives.get(value1);
    if (repr1 == null) {
      return false;
    }

    var repr2 = representatives.get(value2);
    if (!repr1.equals(repr2)) {
      return false;
    }

    return repr1.equals(repr2);
  }

  @Override
  public @Nullable ConcreteExpression checkRelation(V value1, V value2) {
    if (value1.equals(value2)) {
      return refl;
    }

    compute();

    var repr1 = representatives.get(value1);
    if (repr1 == null) {
      return null;
    }

    var repr2 = representatives.get(value2);
    if (!repr1.equals(repr2)) {
      return null;
    }

    List<ConcreteExpression> path1 = computePathToRepr(value1, new ArrayList<>());
    List<ConcreteExpression> path2 = computePathToRepr(value2, new ArrayList<>());
    if (path1.isEmpty()) {
      return pathToExpr(path2);
    }

    if (path2.isEmpty()) {
      return factory.app(sym, true, Collections.singletonList(pathToExpr(path1)));
    }

    return factory.app(trans, true, Arrays.asList(factory.app(sym, true, Collections.singletonList(pathToExpr(path1))), pathToExpr(path2)));
  }
}
