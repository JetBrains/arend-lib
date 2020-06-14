package org.arend.lib.meta.closure;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Pair;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class EqualityClosure<V> implements BinaryRelationClosure<V> {
  private final StdExtension ext;
  private final ConcreteFactory factory;
  private final Map<V, List<Pair<V, ConcreteExpression>>> graph = new HashMap<>();

  public EqualityClosure(StdExtension ext, ConcreteFactory factory) {
    this.ext = ext;
    this.factory = factory;
  }

  @Override
  public void addRelation(V value1, V value2, ConcreteExpression proof) {
    graph.computeIfAbsent(value1, v -> new ArrayList<>()).add(new Pair<>(value2, proof));
    graph.computeIfAbsent(value2, v -> new ArrayList<>()).add(new Pair<>(value1, factory.app(factory.ref(ext.inv.getRef()), true, Collections.singletonList(proof))));
  }

  private List<ConcreteExpression> findPath(V start, V end, Set<V> visited) {
    if (!visited.add(start)) {
      return null;
    }

    if (start.equals(end)) {
      return new ArrayList<>();
    }

    for (Pair<V, ConcreteExpression> pair : graph.get(start)) {
      List<ConcreteExpression> path = findPath(pair.proj1, end, visited);
      if (path != null) {
        path.add(pair.proj2);
        return path;
      }
    }

    return null;
  }

  @Override
  public @Nullable ConcreteExpression checkRelation(V value1, V value2) {
    if (value1.equals(value2)) {
      return factory.ref(ext.prelude.getIdp().getRef());
    }

    List<ConcreteExpression> path = findPath(value1, value2, new HashSet<>());
    if (path == null) {
      return null;
    }

    ConcreteExpression result = null;
    for (ConcreteExpression proof : path) {
      result = result == null ? proof : factory.app(factory.ref(ext.concat.getRef()), true, Arrays.asList(proof, result));
    }
    return result;
  }
}
