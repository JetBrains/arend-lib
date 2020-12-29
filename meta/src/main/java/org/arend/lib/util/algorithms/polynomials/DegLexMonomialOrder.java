package org.arend.lib.util.algorithms.polynomials;

import java.util.Comparator;

public class DegLexMonomialOrder<E> implements Comparator<Monomial<E>> {
  @Override
  public int compare(Monomial<E> m1, Monomial<E> m2) {
    int deg1 = m1.degree(), deg2 = m2.degree();
    if (deg1 != deg2) return deg1 - deg2;
    for (int i = 0; i < m1.numVars(); ++i) {
      if (!m1.degreeVector.get(i).equals(m2.degreeVector.get(i))) {
        return m1.degreeVector.get(i) - m2.degreeVector.get(i);
      }
    }
    return 0;
  }
}
