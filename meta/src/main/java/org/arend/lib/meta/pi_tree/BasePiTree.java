package org.arend.lib.meta.pi_tree;

import org.arend.ext.concrete.expr.ConcreteExpression;

import java.util.List;

public class BasePiTree {
  public final ConcreteExpression head;
  public final ConcreteExpression altHead;
  public final List<Integer> indices;
  public final List<PiTreeNode> subtrees;

  public BasePiTree(ConcreteExpression head, ConcreteExpression altHead, List<Integer> indices, List<PiTreeNode> subtrees) {
    this.head = head;
    this.altHead = altHead;
    this.indices = indices;
    this.subtrees = subtrees;
  }
}
