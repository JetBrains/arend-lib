package org.arend.lib.meta.pi_tree;

import org.arend.ext.concrete.expr.ConcreteExpression;

import java.util.List;

public class PiTreeRoot {
  public final ConcreteExpression head;
  public final ConcreteExpression altHead;
  public final List<Integer> indices;
  public final List<PiTree> subtrees;
  public final boolean isNonDependent;

  public PiTreeRoot(ConcreteExpression head, ConcreteExpression altHead, List<Integer> indices, List<PiTree> subtrees) {
    this.head = head;
    this.altHead = altHead;
    this.indices = indices;
    this.subtrees = subtrees;

    boolean nonDependent = indices.isEmpty();
    if (nonDependent) {
      for (PiTreeRoot subtree : subtrees) {
        if (!subtree.isNonDependent) {
          nonDependent = false;
          break;
        }
      }
    }
    isNonDependent = nonDependent;
  }
}
