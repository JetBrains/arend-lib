package org.arend.lib.meta.pi_tree;

import org.arend.ext.concrete.expr.ConcreteExpression;

import java.util.List;

public class PiTreeRoot extends BasePiTree {
  private final boolean isNonDependent;

  public PiTreeRoot(ConcreteExpression head, ConcreteExpression altHead, List<Integer> indices, List<PiTreeNode> subtrees, boolean isNonDependent) {
    super(head, altHead, indices, subtrees);
    if (isNonDependent) {
      for (PiTreeNode tree : subtrees) {
        if (!(tree.subtrees.isEmpty() && tree.indices.isEmpty())) {
          isNonDependent = false;
          break;
        }
      }
    }
    this.isNonDependent = isNonDependent;
  }

  public boolean isNonDependent() {
    return isNonDependent;
  }
}
