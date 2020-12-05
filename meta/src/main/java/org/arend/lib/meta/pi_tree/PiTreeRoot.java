package org.arend.lib.meta.pi_tree;

import org.arend.ext.concrete.expr.ConcreteExpression;

import java.util.List;

public class PiTreeRoot extends BasePiTree {
  public PiTreeRoot(ConcreteExpression head, ConcreteExpression altHead, List<Integer> indices, List<PiTreeNode> subtrees) {
    super(head, altHead, indices, subtrees);
  }

  public boolean isNonDependent() {
    if (!indices.isEmpty()) {
      return false;
    }
    for (PiTreeNode tree : subtrees) {
      if (!(tree.subtrees.isEmpty() && tree.indices.isEmpty())) {
        return false;
      }
    }
    return true;
  }
}
