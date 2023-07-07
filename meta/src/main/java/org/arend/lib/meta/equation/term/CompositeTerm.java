package org.arend.lib.meta.equation.term;

import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;

import java.util.ArrayList;
import java.util.List;

public class CompositeTerm implements CompiledTerm {
  public List<CompiledTerm> subterms = new ArrayList<>();
  public FunctionMatcher matcher;

  public CompositeTerm() {
  }

  public CompositeTerm(FunctionMatcher matcher) {
    this.matcher = matcher;
  }
}
