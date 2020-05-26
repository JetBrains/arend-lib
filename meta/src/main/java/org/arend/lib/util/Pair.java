package org.arend.lib.util;

import java.util.Objects;

public class Pair<T, S> {
  public final T proj1;
  public final S proj2;

  public Pair(T proj1, S proj2) {
    this.proj1 = proj1;
    this.proj2 = proj2;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    Pair<?, ?> pair = (Pair<?, ?>) o;
    return Objects.equals(proj1, pair.proj1) &&
        Objects.equals(proj2, pair.proj2);
  }

  @Override
  public int hashCode() {
    return Objects.hash(proj1, proj2);
  }
}
