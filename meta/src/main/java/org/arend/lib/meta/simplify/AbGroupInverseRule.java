package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.RewriteMeta;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;
import org.arend.lib.util.Values;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class AbGroupInverseRule implements SimplificationRule {
  private final Values<CoreExpression> values;
  private final ConcreteFactory factory;
  private final StdExtension ext;
  private final ConcreteReferenceExpression refExpr;
  private final FunctionMatcher mulMatcher;
  private final FunctionMatcher ideMatcher;
  private final FunctionMatcher invMatcher;
  // private FunctionMatcher minusMatcher = null;

  public AbGroupInverseRule(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ExpressionTypechecker typechecker, ConcreteReferenceExpression refExpr, ConcreteFactory factory, boolean isCommutative) {
    this.values = new Values<>(typechecker, refExpr);
    this.factory = factory;
    this.ext = ext;
    this.refExpr = refExpr;
    if (isCommutative) {
      this.mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.plus, typechecker, factory, refExpr, ext, 2);
      this.invMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.negative, typechecker, factory, refExpr, ext, 1);
      this.ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.zro, typechecker, factory, refExpr, ext, 0);
    } else {
      this.mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.mul, typechecker, factory, refExpr, ext, 2);
      this.invMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.inverse, typechecker, factory, refExpr, ext, 1);
      this.ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.ide, typechecker, factory, refExpr, ext, 0);
    }
  }

  private interface Term {
  }

  private static class MulTerm implements Term {
    public Term left, right;
    public MulTerm(Term left, Term right) { this.left = left; this.right = right; }

    /*@Override
    public ConcreteExpression getConcrete() {
      var leftConcrete = left.getConcrete();
      var rightConcrete = right.getConcrete();
      return factory.appBuilder();
    }*/
  }

  private static class InvTerm implements Term {
    public Term arg;
    public InvTerm(Term arg) { this.arg = arg; }
  }

  private static class VarTerm implements Term {
    public int index;
    public VarTerm(int index) { this.index = index; }
  }

  private static class IdeTerm implements Term { }

  private Term computeTerm(CoreExpression expression) {
    CoreExpression expr = expression.normalize(NormalizationMode.WHNF);

    List<CoreExpression> args = mulMatcher.match(expr);
    if (args != null) {
      return new MulTerm(computeTerm(args.get(0)), computeTerm(args.get(1)));
    }

    args = invMatcher.match(expr);
    if (args != null) {
      return new InvTerm(computeTerm(args.get(0)));
    }

    if (ideMatcher.match(expr) != null) {
      return new IdeTerm();
    }

    int index = values.addValue(expr);
    return new VarTerm(index);
  }

  private Pair<List<Boolean>, List<Boolean>> findCancellingVarTerms(Term term, Boolean curSign, List<Boolean> curPath, Map<Integer, Pair<List<Boolean>, Boolean>> varsToSignedPath) {
    if (term instanceof VarTerm) {
      var varTerm = (VarTerm)term;
      var varSignedPath = varsToSignedPath.get(varTerm.index);
      if (varSignedPath == null) {
        varsToSignedPath.put(varTerm.index, new Pair<>(curPath, curSign));
        return null;
      }
      if (varSignedPath.proj2 == curSign) {
        return null;
      }
      return new Pair<>(varSignedPath.proj1, curPath);
    }
    if (term instanceof IdeTerm) {
      return null;
    }
    if (term instanceof InvTerm) {
      return findCancellingVarTerms(((InvTerm)term).arg, !curSign, curPath, varsToSignedPath);
    }
    var mulTerm = (MulTerm)term;
    curPath.add(false);
    var res = findCancellingVarTerms(mulTerm.left, curSign, curPath, varsToSignedPath);
    if (res != null) {
      return res;
    }
    curPath.set(curPath.size() - 1, !curPath.get(curPath.size() - 1));
    res = findCancellingVarTerms(mulTerm.right, curSign, curPath, varsToSignedPath);
    curPath.remove(curPath.size() - 1);
    return res;
  }

  private Term moveLeafToTheTop(Term term, List<Boolean> path) {
    if (term instanceof InvTerm) {
      var invTerm = (InvTerm)term;
      var newArg = moveLeafToTheTop(invTerm.arg, path);
      if (newArg == null) return null;
      if (newArg instanceof InvTerm) {
        return ((InvTerm)newArg).arg;
      }
      if (newArg instanceof MulTerm) {
        var leftMulArg = ((MulTerm)newArg).left;
        var rightMulArg = ((MulTerm)newArg).right;
        if (rightMulArg instanceof InvTerm) {
          return new MulTerm(new InvTerm(leftMulArg), ((InvTerm)rightMulArg).arg);
        }
        return new MulTerm(new InvTerm(leftMulArg), new InvTerm(rightMulArg));
      }
    }
    if (term instanceof MulTerm) {
      if (path.isEmpty()) return null;
      var mulTerm = (MulTerm)term;
      if (path.get(0)) {
        var newArg = moveLeafToTheTop(mulTerm.right, path.subList(1, path.size()));
        if (newArg == null) return null;
        if (newArg instanceof MulTerm) {
          return new MulTerm(new MulTerm(mulTerm.left, ((MulTerm)newArg).left), ((MulTerm)newArg).right);
        }
        return new MulTerm(mulTerm.left, newArg);
      }
      var newArg = moveLeafToTheTop(mulTerm.left, path.subList(1, path.size()));
      if (newArg == null) return null;
      if (newArg instanceof MulTerm) {
        return new MulTerm(new MulTerm(((MulTerm)newArg).left, mulTerm.right), ((MulTerm)newArg).right);
      }
      return new MulTerm(mulTerm.right, newArg);
    }
    if (term instanceof VarTerm) {
      return term;
    }
    return null;
  }

  @Override
  public RewriteMeta.EqProofConcrete apply(TypedExpression expression) {
    var term = computeTerm(expression.getExpression());

    return null;
  }
}
