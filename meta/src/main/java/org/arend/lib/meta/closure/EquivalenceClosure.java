package org.arend.lib.meta.closure;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.util.Pair;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class EquivalenceClosure<V> implements BinaryRelationClosure<V> {
  protected final ConcreteExpression refl;
  protected final ConcreteExpression sym;
  protected final ConcreteExpression trans;
  protected final ConcreteFactory factory;
  protected final Map<V, List<Pair<V, ConcreteExpression>>> graph = new HashMap<>();

  public EquivalenceClosure(ConcreteExpression refl, ConcreteExpression sym, ConcreteExpression trans, ConcreteFactory factory) {
    this.refl = refl;
    this.sym = sym;
    this.trans = trans;
    this.factory = factory;
  }

  @Override
  public void addRelation(V value1, V value2, ConcreteExpression proof) {
    graph.computeIfAbsent(value1, v -> new ArrayList<>()).add(new Pair<>(value2, proof));
    if (sym != null) {
      graph.computeIfAbsent(value2, v -> new ArrayList<>()).add(new Pair<>(value1, factory.app(sym, true, Collections.singletonList(proof))));
    }
  }

  protected List<ConcreteExpression> findPath(V start, V end, Set<V> visited) {
    if (!visited.add(start)) {
      return null;
    }

    if (start.equals(end)) {
      return new ArrayList<>();
    }

    List<Pair<V, ConcreteExpression>> pairs = graph.get(start);
    if (pairs == null) {
      return null;
    }

    for (Pair<V, ConcreteExpression> pair : pairs) {
      List<ConcreteExpression> path = findPath(pair.proj1, end, visited);
      if (path != null) {
        path.add(pair.proj2);
        return path;
      }
    }

    return null;
  }

  protected ConcreteExpression pathToExpr(List<ConcreteExpression> path) {
    if (path == null) {
      return null;
    }

    if (path.isEmpty()) {
      return refl;
    }

    ConcreteExpression result = null;
    for (ConcreteExpression proof : path) {
      result = result == null ? proof : factory.app(trans, true, Arrays.asList(proof, result));
    }
    return result;
  }

  public @Nullable List<ConcreteExpression> getPath(V start, V end) {
    return findPath(start, end, new HashSet<>());
  }

  @Override
  public @Nullable ConcreteExpression checkRelation(V value1, V value2) {
    return pathToExpr(findPath(value1, value2, new HashSet<>()));
  }
}
