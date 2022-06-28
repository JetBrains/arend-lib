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

import java.util.List;
import java.util.Map;
import java.util.TreeMap;

public class AbGroupInverseRule implements SimplificationRule {
  private final Values<CoreExpression> values;
  private final ConcreteFactory factory;
  private final StdExtension ext;
  private final FunctionMatcher mulMatcher;
  private final FunctionMatcher ideMatcher;
  private final FunctionMatcher invMatcher;
  private final boolean isAdditive;

  public AbGroupInverseRule(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ConcreteReferenceExpression refExpr, ExpressionTypechecker typechecker, boolean isAdditive) {
    this.values = new Values<>(typechecker, refExpr);
    this.factory = ext.factory;
    this.ext = ext;
    this.isAdditive = isAdditive;
    if (isAdditive) {
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

  private void countVarOccurNums(Term term, Map<Integer, Pair<Integer, Integer>> indToVarOccurNums, boolean curSign) {
    if (term instanceof VarTerm) {
      var varTerm = (VarTerm)term;
      var occurNums = indToVarOccurNums.get(varTerm.index);
      if (occurNums == null) {
        indToVarOccurNums.put(varTerm.index, curSign ? new Pair<>(0, 1) : new Pair<>(1, 0));
        return;
      }
      indToVarOccurNums.put(varTerm.index, curSign ? new Pair<>(occurNums.proj1, occurNums.proj2 + 1) : new Pair<>(occurNums.proj1 + 1, occurNums.proj2));
    } else if (term instanceof InvTerm) {
      var invTerm = (InvTerm)term;
      countVarOccurNums(invTerm.arg, indToVarOccurNums, !curSign);
    } else if (term instanceof MulTerm) {
      var mulTerm = (MulTerm)term;
      countVarOccurNums(mulTerm.left, indToVarOccurNums, curSign);
      countVarOccurNums(mulTerm.right, indToVarOccurNums, curSign);
    }
  }
  private Map<Integer, Integer> varsToRemove(Term term) {
    var indToVarOccurNums = new TreeMap<Integer, Pair<Integer, Integer>>();
    countVarOccurNums(term, indToVarOccurNums, false);
    var result = new TreeMap<Integer, Integer>();
    indToVarOccurNums.forEach((key, value) -> result.put(key, Math.min(value.proj1, value.proj2)));
    return result;
  }

  private Term removeVars(Term term, Map<Integer, Pair<Integer, Integer>> numVarsToRemove, boolean curSign) {
    if (term instanceof VarTerm) {
      var varTerm = (VarTerm) term;
      var numsToRemove = numVarsToRemove.get(varTerm.index);
      if (numsToRemove != null) {
        if (curSign && numsToRemove.proj2 > 0) {
          numVarsToRemove.put(varTerm.index, new Pair<>(numsToRemove.proj1, numsToRemove.proj2 - 1));
          return new IdeTerm();
        }
        if (!curSign && numsToRemove.proj1 > 0) {
          numVarsToRemove.put(varTerm.index, new Pair<>(numsToRemove.proj1 - 1, numsToRemove.proj2));
          return new IdeTerm();
        }
      }
    } else if (term instanceof InvTerm) {
      var invTerm = (InvTerm) term;
      return removeVars(invTerm.arg, numVarsToRemove, !curSign);
    } else if (term instanceof MulTerm) {
      var mulTerm = (MulTerm) term;
      var newLeft = removeVars(mulTerm.left, numVarsToRemove, curSign);
      var newRight = removeVars(mulTerm.right, numVarsToRemove, curSign);
      return new MulTerm(newLeft, newRight);
    }
    return term;
  }

  private Pair<ConcreteExpression, ConcreteExpression> termToConcrete(Term term) {
    if (term == null) return null;
    if (term instanceof IdeTerm) {
      return new Pair<>(factory.ref(isAdditive ? ext.equationMeta.zro.getRef() : ext.equationMeta.ide.getRef()),
              factory.ref(ext.equationMeta.ideGTerm.getRef()));
    } else if (term instanceof VarTerm) {
      return new Pair<>(factory.core(values.getValue(((VarTerm) term).index).computeTyped()),
              factory.appBuilder(factory.ref(ext.equationMeta.varGTerm.getRef())).app(factory.number(((VarTerm) term).index)).build());
    } else if (term instanceof InvTerm) {
      var arg = termToConcrete(((InvTerm) term).arg);
      return new Pair<>(factory.appBuilder(isAdditive ? factory.ref(ext.equationMeta.negative.getRef()) : factory.ref(ext.equationMeta.inverse.getRef()))
                      .app(arg.proj1).build(),
              factory.appBuilder(factory.ref(ext.equationMeta.invGTerm.getRef()))
                      .app(arg.proj2).build());
    } else if (term instanceof MulTerm) {
      var left = termToConcrete(((MulTerm) term).left);
      var right = termToConcrete(((MulTerm) term).right);
      return new Pair<>(factory.appBuilder(isAdditive ? factory.ref(ext.equationMeta.plus.getRef()) : factory.ref(ext.equationMeta.mul.getRef()))
              .app(left.proj1)
              .app(right.proj1).build(),
              factory.appBuilder(factory.ref(ext.equationMeta.mulGTerm.getRef()))
                      .app(left.proj2)
                      .app(right.proj2).build());
    }
    return null;
  }

  @Override
  public RewriteMeta.EqProofConcrete apply(TypedExpression expression) {
    var term = computeTerm(expression.getExpression());
    var concreteTerm = termToConcrete(term);
    var numVarsToRemove = new TreeMap<Integer, Pair<Integer, Integer>>();
    varsToRemove(term).forEach((key, value) -> numVarsToRemove.put(key, new Pair<>(value, value)));
    if (numVarsToRemove.isEmpty()) return null;
    var newTerm = removeVars(term, numVarsToRemove, false);
    var simplifyProof = factory.appBuilder(factory.ref(ext.equationMeta.simplifyCorrectAbInv.getRef()))
            .app(concreteTerm.proj2).build();
    var left = factory.core(expression);
    var right = termToConcrete(newTerm).proj1;
    if (isAdditive) {
      simplifyProof = factory.appBuilder(factory.ref(ext.pmap.getRef()))
              .app(factory.ref(ext.equationMeta.fromGroupToAddGroup.getRef()))
              .app(simplifyProof).build();
    }
    return new RewriteMeta.EqProofConcrete(simplifyProof, left, right);/**/
  }
}
