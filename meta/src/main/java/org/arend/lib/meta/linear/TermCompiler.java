package org.arend.lib.meta.linear;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.equation.EquationMeta;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;
import org.arend.lib.ring.BigRational;
import org.arend.lib.ring.IntRing;
import org.arend.lib.ring.Ring;
import org.arend.lib.util.Values;

import java.math.BigInteger;
import java.util.*;

public class TermCompiler {
  private final FunctionMatcher zroMatcher;
  private final FunctionMatcher ideMatcher;
  private final FunctionMatcher addMatcher;
  private final FunctionMatcher mulMatcher;
  private final FunctionMatcher natCoefMatcher;
  private final FunctionMatcher negativeMatcher;
  private final ConcreteFactory factory;
  private final Values<CoreExpression> values;
  private final EquationMeta meta;
  private final boolean isRat;

  public TermCompiler(CoreClassCallExpression classCall, TypedExpression instance, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
    meta = ext.equationMeta;
    factory = ext.factory.withData(marker);
    boolean isRing = classCall.getDefinition().isSubClassOf(meta.OrderedRing);
    zroMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.ext.zro, typechecker, factory, marker, meta.ext, 0);
    ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.ext.ide, typechecker, factory, marker, meta.ext, 0);
    addMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.plus, typechecker, factory, marker, meta.ext, 2);
    mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.mul, typechecker, factory, marker, meta.ext, 2);
    natCoefMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.natCoef, typechecker, factory, marker, meta.ext, 1);
    negativeMatcher = isRing ? FunctionMatcher.makeFieldMatcher(classCall, instance, meta.negative, typechecker, factory, marker, meta.ext, 1) : null;
    values = new Values<>(typechecker, marker);
    CoreExpression instanceNorm = instance.getExpression().normalize(NormalizationMode.WHNF);
    isRat = instanceNorm instanceof CoreFunCallExpression && ((CoreFunCallExpression) instanceNorm).getDefinition() == ext.equationMeta.RatField;
  }

  public Values<CoreExpression> getValues() {
    return values;
  }

  public boolean isRat() {
    return isRat;
  }

  public Ring getZero() {
    return isRat ? BigRational.ZERO : IntRing.ZERO;
  }

  public Ring getOne() {
    return isRat ? BigRational.ONE : IntRing.ONE;
  }

  public int getNumberOfVariables() {
    return values.getValues().size();
  }

  @SuppressWarnings("unchecked")
  public CompiledTerms compileTerms(CoreExpression expr1, CoreExpression expr2) {
    Pair<ConcreteExpression, List<Ring>> pair1 = compileTerm(expr1);
    Pair<ConcreteExpression, List<Ring>> pair2 = compileTerm(expr2);
    if (isRat) {
      BigInteger lcm = BigInteger.ONE;
      List<BigRational> list1 = (List<BigRational>) (List<?>) pair1.proj2;
      List<BigRational> list2 = (List<BigRational>) (List<?>) pair2.proj2;
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
      return new CompiledTerms(new CompiledTerm(pair1.proj1, coefs1), new CompiledTerm(pair2.proj1, coefs2), lcm);
    } else {
      List<BigInteger> coefs1 = new ArrayList<>(pair1.proj2.size());
      for (Ring ring : pair1.proj2) {
        coefs1.add(((IntRing) ring).number);
      }
      List<BigInteger> coefs2 = new ArrayList<>(pair2.proj2.size());
      for (Ring ring : pair2.proj2) {
        coefs2.add(((IntRing) ring).number);
      }
      return new CompiledTerms(new CompiledTerm(pair1.proj1, coefs1), new CompiledTerm(pair2.proj1, coefs2), BigInteger.ONE);
    }
  }

  private Pair<ConcreteExpression, List<Ring>> compileTerm(CoreExpression expression) {
    Map<Integer, Ring> coefficients = new HashMap<>();
    Ring[] freeCoef = new Ring[] { getZero() };
    ConcreteExpression concrete = computeTerm(expression, coefficients, freeCoef);
    List<Ring> resultCoefs = new ArrayList<>(getNumberOfVariables());
    resultCoefs.add(freeCoef[0]);
    for (int i = 0; i < getNumberOfVariables(); i++) {
      Ring coef = coefficients.get(i);
      resultCoefs.add(coef == null ? getZero() : coef);
    }
    return new Pair<>(concrete, resultCoefs);
  }

  private Pair<Boolean, CoreExpression> checkInt(CoreExpression expr) {
    if (expr instanceof CoreConCallExpression) {
      CoreConstructor constructor = ((CoreConCallExpression) expr).getDefinition();
      if (constructor == meta.ext.prelude.getPos() || constructor == meta.ext.prelude.getNeg()) {
        return new Pair<>(constructor == meta.ext.prelude.getNeg(), ((CoreConCallExpression) expr).getDefCallArguments().get(0));
      }
    } else if (expr instanceof CoreIntegerExpression) {
      return new Pair<>(false, expr);
    }
    return null;
  }

  private BigInteger getInt(CoreExpression expr) {
    Pair<Boolean, CoreExpression> pair = checkInt(expr);
    if (pair == null) return null;
    CoreExpression arg = pair.proj2.normalize(NormalizationMode.WHNF);
    if (!(arg instanceof CoreIntegerExpression)) return null;
    BigInteger number = ((CoreIntegerExpression) arg).getBigInteger();
    return pair.proj1 ? number.negate() : number;
  }

  private ConcreteExpression computeTerm(CoreExpression expression, Map<Integer, Ring> coefficients, Ring[] freeCoef) {
    CoreExpression expr = expression.normalize(NormalizationMode.WHNF);

    if (zroMatcher.match(expr) != null) {
      return factory.ref(meta.zroTerm.getRef());
    }

    List<CoreExpression> addArgs = addMatcher.match(expr);
    if (addArgs != null) {
      return factory.app(factory.ref(meta.addTerm.getRef()), true, computeTerm(addArgs.get(addArgs.size() - 2), coefficients, freeCoef), computeTerm(addArgs.get(addArgs.size() - 1), coefficients, freeCoef));
    }

    if (ideMatcher.match(expr) != null) {
      freeCoef[0] = freeCoef[0].add(getOne());
      return factory.ref(meta.ideTerm.getRef());
    }

    if (negativeMatcher != null) {
      List<CoreExpression> negativeArgs = negativeMatcher.match(expr);
      if (negativeArgs != null) {
        Map<Integer, Ring> newCoefficients = new HashMap<>();
        Ring[] newFreeCoef = new Ring[] { getZero() };
        ConcreteExpression term = computeTerm(negativeArgs.get(0), newCoefficients, newFreeCoef);
        for (Map.Entry<Integer, Ring> entry : newCoefficients.entrySet()) {
          coefficients.compute(entry.getKey(), (k,v) -> v == null ? entry.getValue().negate() : v.subtract(entry.getValue()));
        }
        freeCoef[0] = freeCoef[0].subtract(newFreeCoef[0]);
        return factory.app(factory.ref(meta.negativeTerm.getRef()), true, term);
      }
    }

    boolean isNeg = false;
    List<? extends CoreExpression> coefArgs = null;
    Pair<Boolean, CoreExpression> pair = checkInt(expr);
    if (pair != null) {
      isNeg = pair.proj1;
      coefArgs = Collections.singletonList(pair.proj2);
    }

    if (coefArgs == null) {
      coefArgs = natCoefMatcher.match(expr);
    }
    if (coefArgs != null) {
      CoreExpression arg = coefArgs.get(0).normalize(NormalizationMode.WHNF);
      if (arg instanceof CoreIntegerExpression) {
        BigInteger coef = ((CoreIntegerExpression) arg).getBigInteger();
        if (isNeg) coef = coef.negate();
        freeCoef[0] = freeCoef[0].add(isRat ? BigRational.makeInt(coef) : new IntRing(coef));
        return factory.app(factory.ref(meta.coefTerm.getRef()), true, factory.number(coef));
      }
    }

    List<CoreExpression> mulArgs = mulMatcher.match(expr);
    if (mulArgs != null) {
      int valuesSize = values.getValues().size();
      Map<Integer, Ring> coefficients1 = new HashMap<>(), coefficients2 = new HashMap<>();
      Ring[] freeCoef1 = new Ring[] { getZero() }, freeCoef2 = new Ring[] { getZero() };
      ConcreteExpression leftTerm = computeTerm(mulArgs.get(mulArgs.size() - 2), coefficients1, freeCoef1);
      ConcreteExpression rightTerm = computeTerm(mulArgs.get(mulArgs.size() - 1), coefficients2, freeCoef2);
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
        coefficients.compute(values.addValue(expr), (k,v) -> v == null ? getOne() : v.add(getOne()));
      }
      return factory.app(factory.ref(meta.mulTerm.getRef()), true, leftTerm, rightTerm);
    }

    if (isRat && expr instanceof CoreConCallExpression) {
      CoreConCallExpression conCall = (CoreConCallExpression) expr;
      TypedExpression typedExpr = expr.computeTyped();
      CoreExpression nomExpr = conCall.getDefCallArguments().get(0);
      CoreExpression denomExpr = conCall.getDefCallArguments().get(1);
      if (nomExpr != null && denomExpr != null) {
        BigInteger nom = getInt(nomExpr.normalize(NormalizationMode.WHNF));
        BigInteger denom = getInt(denomExpr.normalize(NormalizationMode.WHNF));
        if (nom != null && denom != null) {
          BigRational coef = BigRational.make(nom, denom);
          if (isNeg) coef = coef.negate();
          freeCoef[0] = freeCoef[0].add(coef);
          return factory.app(factory.ref(meta.coefTerm.getRef()), true, factory.core(typedExpr));
        }
      }
    }

    int index = values.addValue(expr);
    coefficients.compute(index, (k,v) -> v == null ? getOne() : v.add(getOne()));
    return factory.app(factory.ref(meta.varTerm.getRef()), true, factory.number(index));
  }
}
