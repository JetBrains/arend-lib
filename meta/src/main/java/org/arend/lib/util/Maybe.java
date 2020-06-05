package org.arend.lib.util;

import java.util.Objects;

public class Maybe<T> {
  public final T just;

  public Maybe(T just) {
    this.just = just;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    Maybe<?> maybe = (Maybe<?>) o;
    return Objects.equals(just, maybe.just);
  }

  @Override
  public int hashCode() {
    return Objects.hash(just);
  }
}
