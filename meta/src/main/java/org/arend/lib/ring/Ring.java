package org.arend.lib.ring;

public interface Ring {
  Ring add(Ring x);
  Ring multiply(Ring x);
  Ring negate();
  Ring subtract(Ring x);
}
