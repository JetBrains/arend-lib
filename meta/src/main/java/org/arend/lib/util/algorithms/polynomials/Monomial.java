package org.arend.lib.util.algorithms.polynomials;

import java.util.*;

public class Monomial<E> {
  public E coefficient;
  public final List<Integer> degreeVector;
  public final Ring<E> ring;

  public Monomial(E coefficient, List<Integer> degreeVector, Ring<E> ring) {
    this.coefficient = coefficient;
    this.degreeVector = new ArrayList<>(degreeVector);
    this.ring = ring;
  }

  public Monomial(E coefficient, int numVars, Ring<E> ring) {
    this.degreeVector = new ArrayList<>();
    this.coefficient = coefficient;
    this.ring = ring;
    for (int i = 0; i < numVars; ++i) {
      this.degreeVector.add(0);
    }
  }

  public Monomial(Monomial<E> monomial) {
    this.coefficient = monomial.coefficient;
    this.degreeVector = new ArrayList<>(monomial.degreeVector);
    this.ring = monomial.ring;
  }

  public Monomial<E> lcm(Monomial<E> m) {
    int N = numVars();
    var dv = new ArrayList<>(degreeVector);//, dv2 = t2.dv().exponents;
    for (int i = 0; i < N; ++i) {
      int deg = Math.max(dv.get(i), m.degreeVector.get(i));
      dv.set(i, deg);
    }
    return new Monomial<>(ring.lcm(coefficient, m.coefficient), dv, ring);
  }

  public boolean isDivisible(Monomial<E> m) {
    for (int i = 0; i < degreeVector.size(); ++i) {
      if (degreeVector.get(i) < m.degreeVector.get(i)) {
        return false;
      }
    }
    return ring.div(this.coefficient, m.coefficient) != null;
  }

  public boolean degVecEquals(Monomial<E> m) {
    if (m == null) return false;
    return Objects.equals(degreeVector, m.degreeVector);
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    Monomial<?> monomial = (Monomial<?>) o;
    return Objects.equals(coefficient, monomial.coefficient) &&
            Objects.equals(degreeVector, monomial.degreeVector);
  }

  @Override
  public int hashCode() {
    return Objects.hash(coefficient, degreeVector, ring);
  }

  @Override
  public String toString() {
    if (degree() == 0) {
      return coefficient.toString();
    }
    StringBuilder str = new StringBuilder(!coefficient.equals(ring.unit()) ? coefficient.toString() + " * " : "");
    for (int i = 0; i < numVars(); ++i) {
      if (degreeVector.get(i) == 1) {
        str.append("x").append(i + 1);
      } else if (degreeVector.get(i) > 1) {
        str.append("x").append(i + 1).append("^").append(degreeVector.get(i));
      }
    }
    return str.toString();
  }

  public Monomial<E> divideBy(Monomial<E> m) {
    var quot = new Monomial<>(this);
    for (int i = 0; i < degreeVector.size(); ++i) {
      var deg = quot.degreeVector.get(i);
      quot.degreeVector.set(i, deg - m.degreeVector.get(i));
    }
    quot.coefficient = ring.div(coefficient, m.coefficient);
    return quot;
  }

  public Monomial<E> mul(Monomial<E> m) {
    var result = new Monomial<>(ring.mul(coefficient, m.coefficient), new ArrayList<>(), ring);
    for (int i = 0; i < Math.max(degreeVector.size(), m.degreeVector.size()); ++i) {
      int deg = i < degreeVector.size() ? degreeVector.get(i) : 0;
      if (i < m.degreeVector.size()) {
        deg += m.degreeVector.get(i);
      }
      result.degreeVector.add(deg);
    }
    return result;
  }

  public Monomial<E> mul(List<Integer> degreeVector) {
    return mul(new Monomial<>(ring.unit(), degreeVector, ring));
  }

  public int numVars() {
    return degreeVector.size();
  }

  public int degree() {
    int deg = 0;
    for (int d : degreeVector) {
      deg += d;
    }
    return deg;
  }
}
