package org.arend.lib.util;

import java.util.function.Supplier;

public class Lazy<V> {
  private V value;
  private final Supplier<V> supplier;

  public Lazy(Supplier<V> supplier) {
    this.supplier = supplier;
  }

  public V get() {
    if (value != null) {
      return value;
    }
    return value = supplier.get();
  }
}
