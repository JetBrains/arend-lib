package org.arend.lib.meta.linear;

import java.math.BigInteger;

public class CompiledTerms {
  public final CompiledTerm term1;
  public final CompiledTerm term2;
  public final BigInteger lcm;

  public CompiledTerms(CompiledTerm term1, CompiledTerm term2, BigInteger lcm) {
    this.term1 = term1;
    this.term2 = term2;
    this.lcm = lcm;
  }
}
