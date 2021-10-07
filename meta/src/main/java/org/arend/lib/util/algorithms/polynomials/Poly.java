package org.arend.lib.util.algorithms.polynomials;

import org.arend.ext.util.Pair;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

public class Poly<E> {
  public final List<Monomial<E>> monomials = new ArrayList<>();

  public Poly(List<Monomial<E>> monomials) {
    var monCpy = new ArrayList<>(monomials);
    var numVars = monomials.get(0).numVars();
    var ring = monomials.get(0).ring;
    monCpy.sort(new DegLexMonomialOrder<>());

    if (monCpy.get(0).degree() != 0) {
      monCpy.add(0, new Monomial<>(ring.zero(), numVars, ring));
    }

    Monomial<E> lastMon = null;
    Monomial<E> lastAdded = null;
    for (Monomial<E> mon : monCpy) {
      if (!mon.degVecEquals(lastMon)) {
        lastAdded = new Monomial<>(mon);
        this.monomials.add(lastAdded);
      } else {
        assert lastAdded != null;
        lastAdded.coefficient = mon.ring.add(lastAdded.coefficient, mon.coefficient);
      }
      lastMon = mon;
    }

    this.monomials.removeIf(mon -> mon.coefficient.equals(ring.zero()) && mon.degree() != 0);
  }

  public static <E> Poly<E> constant(E c, int varNum, Ring<E> ring) {
    var mono = new Monomial<>(c, varNum, ring);
    return new Poly<>(Collections.singletonList(mono));
  }

  public boolean isZero() {
    return monomials.size() == 1 && monomials.get(0).coefficient.equals(ring().zero());
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    Poly<?> poly = (Poly<?>) o;
    return Objects.equals(monomials, poly.monomials);
  }

  @Override
  public int hashCode() {
    return Objects.hash(monomials);
  }

  @Override
  public String toString() {
    StringBuilder polyStr;
    int startInd = 0;
    if (monomials.get(0).degree() == 0 && monomials.get(0).coefficient.equals(ring().zero()) && monomials.size() > 1) {
      startInd = 1;
    }
    polyStr = new StringBuilder(monomials.get(startInd).toString());
    for (int i = startInd + 1; i < monomials.size(); ++i) {
      if (ring().cmp(monomials.get(i).coefficient, ring().zero()) > 0) {
        polyStr.append("+");
      }
      polyStr.append(monomials.get(i));
    }
    return polyStr.toString();
  }

  public Ring<E> ring() {
    return monomials.get(0).ring;
  }

  public int numVars() {
    return monomials.get(0).numVars();
  }

  public Monomial<E> leadingTerm() {
    return monomials.get(monomials.size() - 1);
  }

  public Poly<E> add(Poly<E> poly) {
    var sumMonomials = new ArrayList<>(monomials);
    sumMonomials.addAll(poly.monomials);
    return new Poly<>(sumMonomials);
  }

  public Poly<E> subtr(Poly<E> poly) {
    return add(poly.mul(new Monomial<>(Ring.negUnit(ring()), numVars(), ring())));
  }

  public Poly<E> subtr(Monomial<E> m) {
    return subtr(new Poly<>(Collections.singletonList(m)));
  }

  public Poly<E> add(Monomial<E> m) {
    return add(new Poly<>(Collections.singletonList(m)));
  }

  public Poly<E> mul(Monomial<E> m) {
    var resultMonos = new ArrayList<Monomial<E>>();
    for (Monomial<E> mon : monomials) {
      resultMonos.add(mon.mul(m));
    }
    return new Poly<>(resultMonos);
  }

  public Poly<E> mul(Poly<E> poly) {
    Poly<E> result = constant(ring().zero(), numVars(), ring());
    for (Monomial<E> mon : monomials) {
      result = result.add(poly.mul(mon));
    }
    return result;
  }

  public Pair<Poly<E>, Poly<E>> divideWRemainder(Poly<E> poly) {
    var rem = new Poly<>(monomials);
    var quot = constant(ring().zero(), numVars(), ring());
    while (!rem.isZero() && rem.leadingTerm().isDivisible(poly.leadingTerm())) {
      var quot_term = rem.leadingTerm().divideBy(poly.leadingTerm());
      rem = rem.subtr(poly.mul(quot_term));
      quot = quot.add(new Poly<>(Collections.singletonList(quot_term)));
    }
    return new Pair<>(quot, rem);
  }

  public List<Poly<E>> divideWRemainder(List<Poly<E>> polys) {
    var rem = new Poly<>(monomials);
    var quotRem = new ArrayList<Poly<E>>();
    for (Poly<E> poly : polys) {
      quotRem.add(Poly.constant(ring().zero(), numVars(), ring()));
    }
    var lastRem = Poly.constant(ring().zero(), numVars(), ring());
    while (!rem.equals(lastRem)) {
      lastRem = rem;
      for (int i = 0; i < polys.size(); ++i) {
        var divres = rem.divideWRemainder(polys.get(i));
        quotRem.set(i, quotRem.get(i).add(divres.proj1));
        rem = divres.proj2;
      }
    }
    quotRem.add(rem);
    return quotRem;
  }
}
