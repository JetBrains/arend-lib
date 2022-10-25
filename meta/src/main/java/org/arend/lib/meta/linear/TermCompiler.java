package org.arend.lib.meta.linear;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreFunctionDefinition;
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
import org.arend.lib.util.Utils;
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
  private final Kind kind;
  private final boolean toInt;
  private final boolean toRat;
  private final TermCompiler subTermCompiler;
  private final ExpressionTypechecker typechecker;
  public final Set<Integer> positiveVars;

  public enum Kind { NAT, INT, RAT, NONE }

  private TermCompiler(CoreClassCallExpression classCall, TypedExpression instance, Kind kind, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values, Set<Integer> positiveVars, boolean toInt, boolean toRat) {
    meta = ext.equationMeta;
    factory = ext.factory.withData(marker);
    boolean isRing = classCall.getDefinition().isSubClassOf(meta.OrderedRing);
    zroMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.ext.zro, typechecker, factory, marker, meta.ext, 0);
    ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.ext.ide, typechecker, factory, marker, meta.ext, 0);
    addMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.plus, typechecker, factory, marker, meta.ext, 2);
    mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.mul, typechecker, factory, marker, meta.ext, 2);
    natCoefMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.natCoef, typechecker, factory, marker, meta.ext, 1);
    negativeMatcher = isRing ? FunctionMatcher.makeFieldMatcher(classCall, instance, meta.negative, typechecker, factory, marker, meta.ext, 1) : null;
    this.values = values;
    this.kind = kind;
    TermCompiler subTermCompiler = null;
    if (kind == Kind.INT || kind == Kind.RAT) {
      CoreFunctionDefinition subInstance = kind == Kind.INT ? meta.ext.equationMeta.NatSemiring : meta.ext.equationMeta.IntRing;
      TypedExpression typed = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(factory.ref(subInstance.getRef()), null));
      if (typed != null) {
        subTermCompiler = new TermCompiler((CoreClassCallExpression) subInstance.getResultType(), typed, kind == Kind.INT ? Kind.NAT : Kind.INT, ext, typechecker, marker, values, positiveVars, kind == Kind.INT, kind == Kind.RAT);
      }
    }
    this.toInt = toInt;
    this.toRat = toRat;
    this.subTermCompiler = subTermCompiler;
    this.typechecker = typechecker;
    this.positiveVars = positiveVars;
  }

  public TermCompiler(CoreClassCallExpression classCall, TypedExpression instance, Kind kind, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
    this(classCall, instance, kind, ext, typechecker, marker, new Values<>(typechecker, marker), new HashSet<>(), false, false);
  }

  public Kind getKind() {
    return kind;
  }

  public boolean isNat() {
    return kind == Kind.NAT;
  }

  public boolean isInt() {
    return kind == Kind.INT;
  }

  public boolean isRat() {
    return kind == Kind.RAT;
  }

  public Values<CoreExpression> getValues() {
    return values;
  }

  public Ring getZero() {
    return kind == Kind.RAT ? BigRational.ZERO : IntRing.ZERO;
  }

  public Ring getOne() {
    return kind == Kind.RAT ? BigRational.ONE : IntRing.ONE;
  }

  public int getNumberOfVariables() {
    return values.getValues().size();
  }

  @SuppressWarnings("unchecked")
  public CompiledTerms compileTerms(CoreExpression expr1, CoreExpression expr2) {
    Pair<ConcreteExpression, List<Ring>> pair1 = compileTerm(expr1);
    Pair<ConcreteExpression, List<Ring>> pair2 = compileTerm(expr2);
    if (kind == Kind.RAT) {
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

  private ConcreteExpression makeAddTerm(List<CoreExpression> args, Map<Integer, Ring> coefficients, Ring[] freeCoef) {
    return factory.app(factory.ref(meta.addTerm.getRef()), true, computeTerm(args.get(args.size() - 2), coefficients, freeCoef), computeTerm(args.get(args.size() - 1), coefficients, freeCoef));
  }

  private ConcreteExpression computeTerm(CoreExpression expression, Map<Integer, Ring> coefficients, Ring[] freeCoef) {
    CoreExpression expr = expression.normalize(NormalizationMode.WHNF);

    if (zroMatcher.match(expr) != null) {
      return factory.ref(meta.zroTerm.getRef());
    }

    List<CoreExpression> addArgs = addMatcher.match(expr);
    if (addArgs != null) {
      return makeAddTerm(addArgs, coefficients, freeCoef);
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
        if (term == null) return null;
        for (Map.Entry<Integer, Ring> entry : newCoefficients.entrySet()) {
          coefficients.compute(entry.getKey(), (k,v) -> v == null ? entry.getValue().negate() : v.subtract(entry.getValue()));
        }
        freeCoef[0] = freeCoef[0].subtract(newFreeCoef[0]);
        return factory.app(factory.ref(meta.negativeTerm.getRef()), true, term);
      }
    }

    if (kind == Kind.RAT && expr instanceof CoreConCallExpression) {
      CoreConCallExpression conCall = (CoreConCallExpression) expr;
      TypedExpression typedExpr = expr.computeTyped();
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
        ConcreteExpression term = subTermCompiler.computeTerm(nomExpr, newCoefficients, newFreeCoef);
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

    if (coefArgs == null && kind != Kind.RAT) {
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
        ConcreteExpression term = subTermCompiler.computeTerm(arg, newCoefficients, newFreeCoef);
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
      int valuesSize = values.getValues().size();
      Map<Integer, Ring> coefficients1 = new HashMap<>(), coefficients2 = new HashMap<>();
      Ring[] freeCoef1 = new Ring[] { getZero() }, freeCoef2 = new Ring[] { getZero() };
      ConcreteExpression leftTerm = computeTerm(mulArgs.get(mulArgs.size() - 2), coefficients1, freeCoef1);
      ConcreteExpression rightTerm = computeTerm(mulArgs.get(mulArgs.size() - 1), coefficients2, freeCoef2);
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
        coefficients.compute(values.addValue(expr), (k,v) -> v == null ? getOne() : v.add(getOne()));
      }
      return factory.app(factory.ref(meta.mulTerm.getRef()), true, leftTerm, rightTerm);
    }

    int index = values.addValue(expr);
    if (toInt) {
      expr = toPos(expr, typechecker, factory, meta.ext);
      if (expr == null) return null;
      positiveVars.add(index);
    } else if (toRat) {
      expr = toRat(expr, typechecker, factory, meta.ext);
      if (expr == null) return null;
    }
    coefficients.compute(index, (k,v) -> v == null ? getOne() : v.add(getOne()));
    return factory.app(factory.ref(meta.varTerm.getRef()), true, factory.number(index));
  }

  public static CoreExpression toPos(CoreExpression expr, ExpressionTypechecker typechecker, ConcreteFactory factory, StdExtension ext) {
    TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(factory.app(factory.ref(ext.prelude.getPos().getRef()), true, factory.core(expr.computeTyped())), null));
    if (result == null) return null;
    return result.getExpression();
  }

  public static CoreExpression toRat(CoreExpression expr, ExpressionTypechecker typechecker, ConcreteFactory factory, StdExtension ext) {
    TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(factory.app(factory.ref(ext.equationMeta.fromInt.getRef()), true, factory.core(expr.computeTyped())), null));
    if (result == null) return null;
    return result.getExpression();
  }
}
