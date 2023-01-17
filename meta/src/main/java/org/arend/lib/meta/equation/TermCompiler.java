package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreIntegerExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.solver.BaseTermCompiler;
import org.arend.lib.meta.solver.RingKind;
import org.arend.lib.ring.Monomial;
import org.arend.lib.util.Values;

import java.math.BigInteger;
import java.util.*;

import static java.util.Collections.singletonList;

public class TermCompiler extends BaseTermCompiler {
  private final CoreClassDefinition forcedClass;
  public final boolean isLattice;
  public final boolean isRing;

  private TermCompiler(CoreClassCallExpression classCall, boolean isRing, boolean isLattice, TypedExpression instance, RingKind kind, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values, Set<Integer> positiveVars, boolean toInt, boolean toRat, CoreClassDefinition forcedClass) {
    super(classCall, isRing, isLattice, instance, kind, ext, typechecker, marker, values, positiveVars, toInt, toRat);
    this.forcedClass = forcedClass;
    this.isLattice = isLattice;
    this.isRing = isRing;
  }

  private TermCompiler(CoreClassCallExpression classCall, boolean isRing, boolean isLattice, TypedExpression instance, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values, CoreClassDefinition forcedClass) {
    super(classCall, isRing, isLattice, instance, ext, typechecker, marker, values);
    this.forcedClass = forcedClass;
    this.isLattice = isLattice;
    this.isRing = isRing;
  }

  public TermCompiler(CoreClassCallExpression classCall, TypedExpression instance, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values, CoreClassDefinition forcedClass) {
    this(classCall, isRing(classCall, ext.equationMeta, forcedClass), isLattice(classCall, ext.equationMeta, forcedClass), instance, ext, typechecker, marker, values, forcedClass);
  }

  private static boolean isLattice(CoreClassCallExpression classCall, EquationMeta meta, CoreClassDefinition forcedClass) {
    return classCall.getDefinition().isSubClassOf(meta.BoundedDistributiveLattice) && (forcedClass == null || forcedClass.isSubClassOf(meta.BoundedDistributiveLattice));
  }

  private static boolean isRing(CoreClassCallExpression classCall, EquationMeta meta, CoreClassDefinition forcedClass) {
    return classCall.getDefinition().isSubClassOf(meta.Ring) && (forcedClass == null || forcedClass.isSubClassOf(meta.Ring));
  }

  @Override
  protected BaseTermCompiler newInstance(CoreClassCallExpression classCall, TypedExpression instance, RingKind kind, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values, Set<Integer> positiveVars, boolean toInt, boolean toRat) {
    return new TermCompiler(classCall, isRing(classCall, ext.equationMeta, forcedClass), isLattice(classCall, ext.equationMeta, forcedClass), instance, kind, ext, typechecker, marker, values, positiveVars, toInt, toRat, forcedClass);
  }

  private TermCompiler getSubTermCompiler() {
    return (TermCompiler) subTermCompiler;
  }

  private ConcreteExpression computeNegative(CoreExpression arg, List<Monomial> nf) {
    List<Monomial> nf1 = new ArrayList<>();
    List<ConcreteExpression> cArgs = Collections.singletonList(computeTerm(arg, nf1));
    Monomial.negate(nf1, nf);
    return factory.app(factory.ref(meta.negativeTerm.getRef()), true, cArgs);
  }

  private ConcreteExpression computeMinus(CoreExpression arg1, CoreExpression arg2, List<Monomial> nf) {
    ConcreteExpression cArg1 = computeTerm(arg1, nf);
    ConcreteExpression cArg2 = computeNegative(arg2, nf);
    return factory.app(factory.ref(meta.addTerm.getRef()), true, cArg1, cArg2);
  }

  public static class CompiledTerm {
    final ConcreteExpression originalExpr;
    final ConcreteExpression concrete;
    final List<Monomial> nf;

    private CompiledTerm(ConcreteExpression concrete, List<Monomial> nf, ConcreteExpression originalExpr) {
      this.concrete = concrete;
      this.nf = nf;
      this.originalExpr = originalExpr;
    }
  }

  public CompiledTerm compileTerm(CoreExpression expression) {
    List<Monomial> nf = new ArrayList<>();
    return new CompiledTerm(computeTerm(expression, nf), nf, factory.core(expression.computeTyped()));
  }

  private ConcreteExpression computeTerm(CoreExpression expression, List<Monomial> nf) {
    CoreExpression expr = expression.normalize(NormalizationMode.WHNF);
    if (zroMatcher.match(expr) != null) {
      return factory.ref(meta.zroTerm.getRef());
    }
    if (ideMatcher.match(expr) != null) {
      nf.add(new Monomial(BigInteger.ONE, Collections.emptyList()));
      return factory.ref(meta.ideTerm.getRef());
    }

    if (subTermCompiler != null && subTermCompiler.minusMatcher != null) {
      List<CoreExpression> minusArgs = subTermCompiler.minusMatcher.match(expr);
      if (minusArgs != null) {
        return getSubTermCompiler().computeMinus(minusArgs.get(0), minusArgs.get(1), nf);
      }
    }

    List<CoreExpression> addArgs = addMatcher.match(expr);
    if (addArgs != null) {
      List<ConcreteExpression> cArgs = new ArrayList<>(2);
      cArgs.add(computeTerm(addArgs.get(0), nf));
      cArgs.add(computeTerm(addArgs.get(1), nf));
      return factory.app(factory.ref(meta.addTerm.getRef()), true, cArgs);
    }

    List<CoreExpression> mulArgs = mulMatcher.match(expr);
    if (mulArgs != null) {
      List<ConcreteExpression> cArgs = new ArrayList<>(2);
      List<Monomial> nf1 = new ArrayList<>();
      List<Monomial> nf2 = new ArrayList<>();
      cArgs.add(computeTerm(mulArgs.get(0), nf1));
      cArgs.add(computeTerm(mulArgs.get(1), nf2));
      List<Monomial> newNF = new ArrayList<>();
      Monomial.multiply(nf1, nf2, newNF);
      Collections.sort(newNF);
      nf.addAll(Monomial.collapse(newNF));
      return factory.app(factory.ref(meta.mulTerm.getRef()), true, cArgs);
    }

    if (isRing) {
      List<CoreExpression> negativeArgs = negativeMatcher.match(expr);
      if (negativeArgs != null) {
        return computeNegative(negativeArgs.get(0), nf);
      }
    }

    Pair<Boolean, CoreExpression> pair = checkInt(expr);
    boolean isNeg = pair != null && pair.proj1;
    List<? extends CoreExpression> coefArgs = pair == null ? null : Collections.singletonList(pair.proj2);

    if (coefArgs == null && kind != RingKind.RAT && !isLattice) {
      coefArgs = natCoefMatcher.match(expr);
    }
    if (coefArgs != null) {
      CoreExpression arg = coefArgs.get(0).normalize(NormalizationMode.WHNF);
      if (arg instanceof CoreIntegerExpression) {
        BigInteger coef = ((CoreIntegerExpression) arg).getBigInteger();
        nf.add(new Monomial(coef, Collections.emptyList()));
        return factory.app(factory.ref(meta.coefTerm.getRef()), true, Collections.singletonList(factory.number(coef)));
      } else if (subTermCompiler != null) {
        List<Monomial> newNF = new ArrayList<>();
        ConcreteExpression term = getSubTermCompiler().computeTerm(arg, newNF);
        if (term != null) {
          if (isNeg) {
            Monomial.negate(newNF, nf);
          } else {
            nf.addAll(newNF);
          }
          return isNeg ? factory.app(factory.ref(meta.negativeTerm.getRef()), true, term) : term;
        }
      }
    }

    int index = values.addValue(expr);
    nf.add(new Monomial(BigInteger.ONE, Collections.singletonList(index)));
    return factory.app(factory.ref(meta.varTerm.getRef()), true, singletonList(factory.number(index)));
  }
}
