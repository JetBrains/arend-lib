package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.RewriteMeta;
import org.arend.lib.meta.equation.datafactory.GroupDataFactory;
import org.arend.lib.meta.equation.term.CompiledTerm;
import org.arend.lib.meta.equation.term.CompositeTerm;
import org.arend.lib.meta.equation.term.VarTerm;

import java.util.Arrays;

public class GroupInverseRule extends GroupRuleBase {

  public GroupInverseRule(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ConcreteReferenceExpression refExpr, ExpressionTypechecker typechecker, boolean isAdditive) {
    super(instance, classCall, ext, refExpr, typechecker, isAdditive, false);
  }

  private boolean isInNF(CompiledTerm term) {
    if (term instanceof VarTerm) return true;
    if (term instanceof CompositeTerm compositeTerm) {
      if (compositeTerm.matcher == mulMatcher) {
        return isInNF(compositeTerm.subterms.get(0)) && isInNF(compositeTerm.subterms.get(1));
      }
      if (compositeTerm.matcher == invMatcher) {
        return !(compositeTerm.subterms.get(0) instanceof CompositeTerm);
      }
      return true;
    }
    return false;
  }

  private int countLeaves(CompiledTerm term) {
    if (term instanceof VarTerm) return 1;
    if (term instanceof CompositeTerm compositeTerm) {
      if (compositeTerm.matcher == mulMatcher) {
        return countLeaves(compositeTerm.subterms.get(0)) + countLeaves(compositeTerm.subterms.get(1));
      }
      if (compositeTerm.matcher == invMatcher) {
        return (compositeTerm.subterms.get(0) instanceof CompositeTerm) ? 0 : 1;
      }
    }
    return 0;
  }

  private static class Leaf {
    public boolean isInv;
    public VarTerm var;
    public Leaf(boolean isInv, VarTerm var) { this.isInv = isInv; this.var = var; }
  }/**/

  private Pair<Integer, Pair<Leaf, Integer>> findFstLeafToRemove(CompiledTerm term, Leaf lastLeaf, int lastLeafInd) {
    if (term instanceof VarTerm varTerm) {
      if (lastLeaf != null && lastLeaf.isInv && varTerm.index == lastLeaf.var.index) {
        return new Pair<>(lastLeafInd - 1, null);
      }
      return new Pair<>(null, new Pair<>(new Leaf(false, varTerm), lastLeafInd - 1));
    }
    if (term instanceof CompositeTerm compositeTerm) {
      if (compositeTerm.matcher == mulMatcher) {
        var rightRes = findFstLeafToRemove(compositeTerm.subterms.get(1), lastLeaf, lastLeafInd);
        if (rightRes.proj1 != null) return new Pair<>(rightRes.proj1, null);
        var leftRes = findFstLeafToRemove(compositeTerm.subterms.get(0), rightRes.proj2.proj1, rightRes.proj2.proj2);
        if (leftRes.proj1 != null) return new Pair<>(leftRes.proj1, null);
        return new Pair<>(null, leftRes.proj2);
      }
      if (compositeTerm.matcher == invMatcher) {
        if (compositeTerm.subterms.get(0) instanceof VarTerm varTerm) {
          if (lastLeaf != null && !lastLeaf.isInv && varTerm.index == lastLeaf.var.index) {
            return new Pair<>(lastLeafInd - 1, null);
          }
          return new Pair<>(null, new Pair<>(new Leaf(true, varTerm), lastLeafInd - 1));
        }
      }
    }
    return new Pair<>(null, new Pair<>(lastLeaf, lastLeafInd));
  }

  private CompiledTerm removePair(CompiledTerm term, int fstIndToRemove) {
    if (term instanceof VarTerm) {
      if (fstIndToRemove <= 1) return null;
      return term;
    }

    if (term instanceof CompositeTerm compositeTerm) {
      if (compositeTerm.matcher == mulMatcher) {
        var left = compositeTerm.subterms.get(0);
        var right = compositeTerm.subterms.get(1);
        int numLeavesLeft = countLeaves(left);
        var result = new CompositeTerm();
        result.matcher = mulMatcher;
        if (fstIndToRemove < numLeavesLeft) {
          var leftRes = removePair(compositeTerm.subterms.get(0), fstIndToRemove);
          if (leftRes == null) {
            return right;
          }
          result.subterms.add(leftRes);
          result.subterms.add(right);
          return result;
        }
        if (fstIndToRemove == numLeavesLeft) {
          var leftRes = removePair(compositeTerm.subterms.get(0), numLeavesLeft);
          var rightRes = removePair(compositeTerm.subterms.get(1), 0);
          if (leftRes == null) return rightRes;
          if (rightRes == null) return leftRes;
          result.subterms.add(leftRes);
          result.subterms.add(rightRes);
          return result;
        }
        var rightRes = removePair(compositeTerm.subterms.get(1), fstIndToRemove - numLeavesLeft);
        if (rightRes == null) {
          return left;
        }
        result.subterms.add(left);
        result.subterms.add(rightRes);
        return result;
      }
    }

    return null;
  }

  private CompiledTerm simplify(CompiledTerm term) {
    if (!isInNF(term)) return null;

    var leafToRemove = findFstLeafToRemove(term, null, countLeaves(term) + 1).proj1;
    if (leafToRemove == null) return null;

    var newTerm = removePair(term, leafToRemove);
    if (newTerm == null) return new CompositeTerm(ideMatcher);
    return newTerm;
  }

  @Override
  public RewriteMeta.EqProofConcrete apply(TypedExpression expression) {
    var term = CompiledTerm.compile(expression.getExpression(), Arrays.asList(mulMatcher, invMatcher, ideMatcher), values);
    var newTerm = simplify(term);
    if (newTerm == null) return null;
    var concreteTerm = CompiledTerm.termToConcrete(term, x -> {
      if (x == mulMatcher) {
        return factory.ref(ext.equationMeta.mulGTerm.getRef());
      }
      if (x == invMatcher) {
        return factory.ref(ext.equationMeta.invGTerm.getRef());
      }
      return factory.ref(ext.equationMeta.ideGTerm.getRef());
    }, ind -> factory.appBuilder(factory.ref(ext.equationMeta.varGTerm.getRef())).app(factory.number(ind)).build(), factory);
    if (concreteTerm == null) return null;
    var simplifyProof = factory.appBuilder(factory.ref(ext.equationMeta.simplifyCorrectInv.getRef()))
      .app(factory.ref(dataRef), false)
      .app(concreteTerm).build();
    var left = factory.core(expression);
    var right = CompiledTerm.termToConcrete(newTerm, x -> {
      if (x == mulMatcher) {
        return isAdditive ? factory.ref(ext.equationMeta.plus.getRef()) : factory.ref(ext.equationMeta.mul.getRef());
      }
      if (x == invMatcher) {
        return isAdditive ? factory.ref(ext.equationMeta.negative.getRef()) : factory.ref(ext.equationMeta.inverse.getRef());
      }
      return factory.ref(isAdditive ? ext.equationMeta.zro.getRef() : ext.equationMeta.ide.getRef());
    }, ind -> factory.core(values.getValue(ind).computeTyped()), factory);
    return new RewriteMeta.EqProofConcrete(simplifyProof, left, right);
  }
}
