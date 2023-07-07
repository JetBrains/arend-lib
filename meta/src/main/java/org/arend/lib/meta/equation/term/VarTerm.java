package org.arend.lib.meta.equation.term;

public class VarTerm implements CompiledTerm {
  public int index;

  public VarTerm(int index) {
    this.index = index;
  }
}
