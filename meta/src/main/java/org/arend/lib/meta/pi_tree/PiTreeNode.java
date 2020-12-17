package org.arend.lib.meta.pi_tree;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreParameter;

import java.util.List;

public class PiTreeNode extends BasePiTree {
  public final CoreParameter parameter;

  public PiTreeNode(CoreParameter parameter, ConcreteExpression head, ConcreteExpression altHead, List<Integer> indices, List<PiTreeNode> subtrees) {
    super(head, altHead, indices, subtrees);
    this.parameter = parameter;
  }
}
