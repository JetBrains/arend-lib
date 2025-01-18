package org.arend.lib.meta.linear;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.solver.BaseTermCompiler;
import org.arend.lib.meta.solver.RingKind;
import org.arend.lib.ring.BigRational;
import org.arend.lib.ring.IntRing;
import org.arend.lib.ring.Ring;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;

import java.math.BigInteger;
import java.util.*;

public class TermCompiler extends BaseTermCompiler {
  private TermCompiler(CoreClassCallExpression classCall, TypedExpression instance, RingKind kind, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values, Set<Integer> positiveVars, boolean toInt, boolean toRat) {
    super(classCall, classCall.getDefinition().isSubClassOf(ext.equationMeta.OrderedRing), false, instance, kind, ext, typechecker, marker, values, positiveVars, toInt, toRat);
  }

  public TermCompiler(CoreClassCallExpression classCall, TypedExpression instance, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
    super(classCall, classCall.getDefinition().isSubClassOf(ext.equationMeta.OrderedRing), false, instance, ext, typechecker, marker, new Values<>(typechecker, marker));
  }

  @Override
  protected BaseTermCompiler newInstance(CoreClassCallExpression classCall, TypedExpression instance, RingKind kind, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values, Set<Integer> positiveVars, boolean toInt, boolean toRat) {
    return new TermCompiler(classCall, instance, kind, ext, typechecker, marker, values, positiveVars, toInt, toRat);
  }

  private TermCompiler getSubTermCompiler() {
    return (TermCompiler) subTermCompiler;
  }

  public RingKind getKind() {
    return kind;
  }

  public boolean isNat() {
    return kind == RingKind.NAT;
  }

  public boolean isInt() {
    return kind == RingKind.INT;
  }

  public Values<CoreExpression> getValues() {
    return values;
  }

  public Ring getZero() {
    return kind == RingKind.RAT || kind == RingKind.RAT_ALG ? BigRational.ZERO : IntRing.ZERO;
  }

  public Ring getOne() {
    return kind == RingKind.RAT || kind == RingKind.RAT_ALG ? BigRational.ONE : IntRing.ONE;
  }

  public int getNumberOfVariables() {
    return values.getValues().size();
  }

  private record MyCompiledTerm(ConcreteExpression concrete, List<Ring> coefficients, Set<Integer> vars) {}

  @SuppressWarnings("unchecked")
  public CompiledTerms compileTerms(CoreExpression expr1, CoreExpression expr2) {
    MyCompiledTerm term1 = compileTerm(expr1);
    MyCompiledTerm term2 = compileTerm(expr2);
    if (kind == RingKind.RAT || kind == RingKind.RAT_ALG) {
      BigInteger lcm = BigInteger.ONE;
      List<BigRational> list1 = (List<BigRational>) (List<?>) term1.coefficients;
      List<BigRational> list2 = (List<BigRational>) (List<?>) term2.coefficients;
      for (BigRational rat : list1) {
        lcm = lcm.divide(lcm.gcd(rat.denom)).multiply(rat.denom);
      }
      for (BigRational rat : list2) {
        lcm = lcm.divide(lcm.gcd(rat.denom)).multiply(rat.denom);
      }
      List<BigInteger> coefs1 = new ArrayList<>(list1.size());
      for (BigRational rat : list1) {
        coefs1.add(rat.nom.multiply(lcm.divide(rat.denom)));
      }
      List<BigInteger> coefs2 = new ArrayList<>(list2.size());
      for (BigRational rat : list2) {
        coefs2.add(rat.nom.multiply(lcm.divide(rat.denom)));
      }
      return new CompiledTerms(new CompiledTerm(term1.concrete, coefs1, term1.vars), new CompiledTerm(term2.concrete, coefs2, term2.vars), lcm);
    } else {
      List<BigInteger> coefs1 = new ArrayList<>(term1.coefficients.size());
      for (Ring ring : term1.coefficients) {
        coefs1.add(((IntRing) ring).number);
      }
      List<BigInteger> coefs2 = new ArrayList<>(term2.coefficients.size());
      for (Ring ring : term2.coefficients) {
        coefs2.add(((IntRing) ring).number);
      }
      return new CompiledTerms(new CompiledTerm(term1.concrete, coefs1, term1.vars), new CompiledTerm(term2.concrete, coefs2, term2.vars), BigInteger.ONE);
    }
  }

  private MyCompiledTerm compileTerm(CoreExpression expression) {
    Map<Integer, Ring> coefficients = new HashMap<>();
    Ring[] freeCoef = new Ring[] { getZero() };
    Set<Integer> vars = new HashSet<>();
    ConcreteExpression concrete = computeTerm(expression, coefficients, freeCoef, vars);
    List<Ring> resultCoefs = new ArrayList<>(getNumberOfVariables());
    resultCoefs.add(freeCoef[0]);
    for (int i = 0; i < getNumberOfVariables(); i++) {
      Ring coef = coefficients.get(i);
      resultCoefs.add(coef == null ? getZero() : coef);
    }
    return new MyCompiledTerm(concrete, resultCoefs, vars);
  }

  private ConcreteExpression computeNegative(CoreExpression arg, Map<Integer, Ring> coefficients, Ring[] freeCoef, Set<Integer> vars) {
    Map<Integer, Ring> newCoefficients = new HashMap<>();
    Ring[] newFreeCoef = new Ring[] { getZero() };
    ConcreteExpression term = computeTerm(arg, newCoefficients, newFreeCoef, vars);
    if (term == null) return null;
    for (Map.Entry<Integer, Ring> entry : newCoefficients.entrySet()) {
      coefficients.compute(entry.getKey(), (k,v) -> v == null ? entry.getValue().negate() : v.subtract(entry.getValue()));
    }
    freeCoef[0] = freeCoef[0].subtract(newFreeCoef[0]);
    return factory.app(factory.ref(meta.negativeTerm.getRef()), true, term);
  }

  private ConcreteExpression computePlus(CoreExpression arg1, CoreExpression arg2, Map<Integer, Ring> coefficients, Ring[] freeCoef, Set<Integer> vars) {
    return factory.app(factory.ref(meta.addTerm.getRef()), true, computeTerm(arg1, coefficients, freeCoef, vars), computeTerm(arg2, coefficients, freeCoef, vars));
  }

  private ConcreteExpression computeMinus(CoreExpression arg1, CoreExpression arg2, Map<Integer, Ring> coefficients, Ring[] freeCoef, Set<Integer> vars) {
    ConcreteExpression cArg1 = computeTerm(arg1, coefficients, freeCoef, vars);
    ConcreteExpression cArg2 = computeNegative(arg2, coefficients, freeCoef, vars);
    return factory.app(factory.ref(meta.addTerm.getRef()), true, cArg1, cArg2);
  }

  private ConcreteExpression computeMul(CoreExpression arg1, CoreExpression arg2, CoreExpression expr, Map<Integer, Ring> coefficients, Ring[] freeCoef, Set<Integer> vars) {
    int valuesSize = values.getValues().size();
    Map<Integer, Ring> coefficients1 = new HashMap<>(), coefficients2 = new HashMap<>();
    Ring[] freeCoef1 = new Ring[] { getZero() }, freeCoef2 = new Ring[] { getZero() };
    ConcreteExpression leftTerm = computeTerm(arg1, coefficients1, freeCoef1, vars);
    ConcreteExpression rightTerm = computeTerm(arg2, coefficients2, freeCoef2, vars);
    if (leftTerm == null || rightTerm == null) return null;
    if (coefficients1.isEmpty() && coefficients2.isEmpty()) {
      freeCoef[0] = freeCoef[0].add(freeCoef1[0].multiply(freeCoef2[0]));
    } else if (coefficients1.isEmpty() || coefficients2.isEmpty()) {
      Ring coef = coefficients1.isEmpty() ? freeCoef1[0] : freeCoef2[0];
      for (Map.Entry<Integer, Ring> entry : coefficients1.entrySet()) {
        Ring newCoef = entry.getValue().multiply(coef);
        coefficients.compute(entry.getKey(), (k,v) -> v == null ? newCoef : v.add(newCoef));
      }
      for (Map.Entry<Integer, Ring> entry : coefficients2.entrySet()) {
        Ring newCoef = entry.getValue().multiply(coef);
        coefficients.compute(entry.getKey(), (k,v) -> v == null ? newCoef : v.add(newCoef));
      }
      freeCoef[0] = freeCoef[0].add(freeCoef1[0].multiply(freeCoef2[0]));
    } else {
      values.getValues().subList(valuesSize, values.getValues().size()).clear();
      return computeVal(expr, coefficients, vars);
    }
    return factory.app(factory.ref(meta.mulTerm.getRef()), true, leftTerm, rightTerm);
  }

  private ConcreteExpression computeVal(CoreExpression expr, Map<Integer, Ring> coefficients, Set<Integer> vars) {
    if (toInt) {
      expr = toPos(expr, typechecker, factory, meta.ext);
      if (expr == null) return null;
    } else if (toRat) {
      expr = toRat(expr, typechecker, factory, meta.ext);
      if (expr == null) return null;
    }
    int index = values.addValue(expr);
    vars.add(index);
    if (toInt) {
      positiveVars.add(index);
    }
    coefficients.compute(index, (k,v) -> v == null ? getOne() : v.add(getOne()));
    return factory.app(factory.ref(meta.varTerm.getRef()), true, factory.number(index));
  }

  private ConcreteExpression computeTerm(CoreExpression expression, Map<Integer, Ring> coefficients, Ring[] freeCoef, Set<Integer> vars) {
    CoreExpression expr = expression.getUnderlyingExpression();
    if (expr instanceof CoreAppExpression || expr instanceof CoreFieldCallExpression) {
      CoreFieldCallExpression fieldCall = null;
      CoreExpression arg1 = null;
      CoreExpression arg2 = null;
      if (expr instanceof CoreFieldCallExpression) {
        fieldCall = (CoreFieldCallExpression) expr;
      } else {
        CoreExpression fun = ((CoreAppExpression) expr).getFunction().getUnderlyingExpression();
        if (fun instanceof CoreFieldCallExpression) {
          fieldCall = (CoreFieldCallExpression) fun;
          arg1 = ((CoreAppExpression) expr).getArgument();
        } else if (fun instanceof CoreAppExpression) {
          CoreExpression fun2 = ((CoreAppExpression) fun).getFunction().getUnderlyingExpression();
          if (fun2 instanceof CoreFieldCallExpression) {
            fieldCall = (CoreFieldCallExpression) fun2;
            arg1 = ((CoreAppExpression) fun).getArgument();
            arg2 = ((CoreAppExpression) expr).getArgument();
          }
        }
      }
      if (fieldCall != null) {
        CoreClassField field = fieldCall.getDefinition();
        if (((field == meta.ext.zro || field == meta.ext.ide) && arg1 == null || (field == meta.plus || field == meta.mul) && arg2 != null || field == meta.negative && arg1 != null && arg2 == null) && typechecker.compare(fieldCall.getArgument(), instance, CMP.EQ, marker, false, true, false)) {
          if (field == meta.ext.zro) {
            return factory.ref(meta.zroTerm.getRef());
          } else if (field == meta.ext.ide) {
            freeCoef[0] = freeCoef[0].add(getOne());
            return factory.ref(meta.ideTerm.getRef());
          } else if (field == meta.negative) {
            return computeNegative(arg1, coefficients, freeCoef, vars);
          } else if (field == meta.plus) {
            return computePlus(arg1, arg2, coefficients, freeCoef, vars);
          } else if (field == meta.mul) {
            return computeMul(arg1, arg2, expr, coefficients, freeCoef, vars);
          }
        }
      }
    }
    expr = expr.normalize(NormalizationMode.WHNF);

    if (zroMatcher.match(expr) != null) {
      return factory.ref(meta.zroTerm.getRef());
    }

    List<CoreExpression> addArgs = addMatcher.match(expr);
    if (addArgs != null) {
      return computePlus(addArgs.get(addArgs.size() - 2), addArgs.get(addArgs.size() - 1), coefficients, freeCoef, vars);
    }

    if (ideMatcher.match(expr) != null) {
      freeCoef[0] = freeCoef[0].add(getOne());
      return factory.ref(meta.ideTerm.getRef());
    }

    if (subTermCompiler != null && subTermCompiler.minusMatcher != null) {
      List<CoreExpression> minusArgs = subTermCompiler.minusMatcher.match(expr);
      if (minusArgs != null) {
        return getSubTermCompiler().computeMinus(minusArgs.get(0), minusArgs.get(1), coefficients, freeCoef, vars);
      }
    }

    if (negativeMatcher != null) {
      List<CoreExpression> negativeArgs = negativeMatcher.match(expr);
      if (negativeArgs != null) {
        return computeNegative(negativeArgs.get(0), coefficients, freeCoef, vars);
      }
    }

    CoreExpression expr1 = kind == RingKind.RAT ? expr : null;
    if (ratAlgebraMatcher != null) {
      List<CoreExpression> ratAlgebraArgs = ratAlgebraMatcher.match(expr);
      if (ratAlgebraArgs != null) {
        expr1 = ratAlgebraArgs.get(0).normalize(NormalizationMode.WHNF);
      }
    }
    if (expr1 instanceof CoreConCallExpression conCall) {
      TypedExpression typedExpr = expr1.computeTyped();
      CoreExpression nomExpr = conCall.getDefCallArguments().get(0).normalize(NormalizationMode.WHNF);
      CoreExpression denomExpr = conCall.getDefCallArguments().get(1).normalize(NormalizationMode.WHNF);
      BigInteger nom = getInt(nomExpr);
      BigInteger denom = getInt(denomExpr);
      if (nom != null && denom != null) {
        freeCoef[0] = freeCoef[0].add(BigRational.make(nom, denom));
        return factory.app(factory.ref(meta.coefTerm.getRef()), true, factory.core(typedExpr));
      }
      if (denom != null && denom.equals(BigInteger.ONE) && subTermCompiler != null) {
        Map<Integer, Ring> newCoefficients = new HashMap<>();
        Ring[] newFreeCoef = new Ring[] { IntRing.ZERO };
        ConcreteExpression term = getSubTermCompiler().computeTerm(nomExpr, newCoefficients, newFreeCoef, vars);
        if (term != null) {
          for (Map.Entry<Integer, Ring> entry : newCoefficients.entrySet()) {
            BigRational value = BigRational.makeInt(((IntRing) entry.getValue()).number);
            coefficients.compute(entry.getKey(), (k,v) -> v == null ? value : v.add(value));
          }
          freeCoef[0] = freeCoef[0].add(BigRational.makeInt(((IntRing) newFreeCoef[0]).number));
          return term;
        }
      }
    }

    Pair<Boolean, CoreExpression> pair = checkInt(expr);
    boolean isNeg = pair != null && pair.proj1;
    List<? extends CoreExpression> coefArgs = pair == null ? null : Collections.singletonList(pair.proj2);

    if (coefArgs == null && kind != RingKind.RAT && kind != RingKind.RAT_ALG) {
      coefArgs = natCoefMatcher.match(expr);
    }
    if (coefArgs != null) {
      CoreExpression arg = coefArgs.get(0).normalize(NormalizationMode.WHNF);
      if (arg instanceof CoreIntegerExpression) {
        BigInteger coef = ((CoreIntegerExpression) arg).getBigInteger();
        if (isNeg) coef = coef.negate();
        freeCoef[0] = freeCoef[0].add(new IntRing(coef));
        return factory.app(factory.ref(meta.coefTerm.getRef()), true, factory.number(coef));
      } else if (subTermCompiler != null) {
        Map<Integer, Ring> newCoefficients = new HashMap<>();
        Ring[] newFreeCoef = new Ring[] { getZero() };
        ConcreteExpression term = getSubTermCompiler().computeTerm(arg, newCoefficients, newFreeCoef, vars);
        if (term != null) {
          for (Map.Entry<Integer, Ring> entry : newCoefficients.entrySet()) {
            coefficients.compute(entry.getKey(), (k,v) -> v == null ? (isNeg ? entry.getValue().negate() : entry.getValue()) : isNeg ? v.subtract(entry.getValue()) : v.add(entry.getValue()));
          }
          freeCoef[0] = isNeg ? freeCoef[0].subtract(newFreeCoef[0]) : freeCoef[0].add(newFreeCoef[0]);
          return isNeg ? factory.app(factory.ref(meta.negativeTerm.getRef()), true, term) : term;
        }
      }
    }

    List<CoreExpression> mulArgs = mulMatcher.match(expr);
    if (mulArgs != null) {
      return computeMul(mulArgs.get(mulArgs.size() - 2), mulArgs.get(mulArgs.size() - 1), expr, coefficients, freeCoef, vars);
    }

    return computeVal(expr, coefficients, vars);
  }

  public static CoreExpression toPos(CoreExpression expr, ExpressionTypechecker typechecker, ConcreteFactory factory, StdExtension ext) {
    TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(factory.app(factory.ref(ext.prelude.getPosRef()), true, factory.core(expr.computeTyped())), null));
    return result == null ? null : result.getExpression();
  }

  public static CoreExpression toRat(CoreExpression expr, ExpressionTypechecker typechecker, ConcreteFactory factory, StdExtension ext) {
    TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(factory.app(factory.ref(ext.equationMeta.fromInt.getRef()), true, factory.core(expr.computeTyped())), null));
    return result == null ? null : result.getExpression();
  }

  public static CoreExpression toRatAlgebra(CoreExpression expr, ExpressionTypechecker typechecker, ConcreteFactory factory, StdExtension ext) {
    TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(factory.app(factory.ref(ext.linearSolverMeta.coefMap.getRef()), true, factory.core(expr.computeTyped())), null));
    return result == null ? null : result.getExpression();
  }
}
