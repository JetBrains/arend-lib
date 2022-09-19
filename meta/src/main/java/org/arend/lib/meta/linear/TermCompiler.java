package org.arend.lib.meta.linear;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreIntegerExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.equation.EquationMeta;
import org.arend.lib.meta.equation.binop_matcher.DefinitionFunctionMatcher;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;
import org.arend.lib.util.Values;

import java.math.BigInteger;
import java.util.*;

public class TermCompiler {
  private final FunctionMatcher zroMatcher;
  private final FunctionMatcher ideMatcher;
  private final FunctionMatcher addMatcher;
  private final FunctionMatcher mulMatcher;
  private final FunctionMatcher natCoefMatcher;
  private final FunctionMatcher intCoefMatcher;
  private final FunctionMatcher negativeMatcher;
  private final ConcreteFactory factory;
  private final Values<CoreExpression> values;
  private final EquationMeta meta;

  public TermCompiler(CoreClassCallExpression classCall, TypedExpression instance, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
    meta = ext.equationMeta;
    factory = ext.factory.withData(marker);
    boolean isRing = classCall.getDefinition().isSubClassOf(meta.Ring);
    zroMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.zro, typechecker, factory, marker, meta.ext, 0);
    ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.ide, typechecker, factory, marker, meta.ext, 0);
    addMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.plus, typechecker, factory, marker, meta.ext, 2);
    mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.mul, typechecker, factory, marker, meta.ext, 2);
    natCoefMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.natCoef, typechecker, factory, marker, meta.ext, 1);
    intCoefMatcher = isRing ? new DefinitionFunctionMatcher(meta.intCoef, 1) : null;
    negativeMatcher = isRing ? FunctionMatcher.makeFieldMatcher(classCall, instance, meta.negative, typechecker, factory, marker, meta.ext, 1) : null;
    values = new Values<>(typechecker, marker);
  }

  public Values<CoreExpression> getValues() {
    return values;
  }

  public int getNumberOfVariables() {
    return values.getValues().size();
  }

  public CompiledTerm compileTerm(CoreExpression expression) {
    Map<Integer, BigInteger> coefficients = new HashMap<>();
    BigInteger[] freeCoef = new BigInteger[] { BigInteger.ZERO };
    ConcreteExpression concrete = computeTerm(expression, coefficients, freeCoef);
    List<BigInteger> resultCoefs = new ArrayList<>(getNumberOfVariables());
    resultCoefs.add(freeCoef[0]);
    for (int i = 0; i < getNumberOfVariables(); i++) {
      BigInteger coef = coefficients.get(i);
      resultCoefs.add(coef == null ? BigInteger.ZERO : coef);
    }
    return new CompiledTerm(concrete, resultCoefs);
  }

  private ConcreteExpression computeTerm(CoreExpression expression, Map<Integer, BigInteger> coefficients, BigInteger[] freeCoef) {
    CoreExpression expr = expression.normalize(NormalizationMode.WHNF);

    if (zroMatcher.match(expr) != null) {
      return factory.ref(meta.zroTerm.getRef());
    }

    List<CoreExpression> addArgs = addMatcher.match(expr);
    if (addArgs != null) {
      return factory.app(factory.ref(meta.addTerm.getRef()), true, computeTerm(addArgs.get(addArgs.size() - 2), coefficients, freeCoef), computeTerm(addArgs.get(addArgs.size() - 1), coefficients, freeCoef));
    }

    if (ideMatcher.match(expr) != null) {
      freeCoef[0] = freeCoef[0].add(BigInteger.ONE);
      return factory.ref(meta.ideTerm.getRef());
    }

    List<CoreExpression> coefArgs = intCoefMatcher == null ? null : intCoefMatcher.match(expr);
    if (coefArgs == null) {
      coefArgs = natCoefMatcher == null ? null : natCoefMatcher.match(expr);
    }
    if (coefArgs != null) {
      CoreExpression arg = coefArgs.get(0).normalize(NormalizationMode.WHNF);
      if (arg instanceof CoreIntegerExpression) {
        BigInteger coef = ((CoreIntegerExpression) arg).getBigInteger();
        freeCoef[0] = freeCoef[0].add(coef);
        return factory.app(factory.ref(meta.coefTerm.getRef()), true, Collections.singletonList(factory.number(coef)));
      }
    }

    List<CoreExpression> mulArgs = mulMatcher.match(expr);
    if (mulArgs != null) {
      int valuesSize = values.getValues().size();
      Map<Integer, BigInteger> coefficients1 = new HashMap<>(), coefficients2 = new HashMap<>();
      BigInteger[] freeCoef1 = new BigInteger[] { BigInteger.ZERO }, freeCoef2 = new BigInteger[] { BigInteger.ZERO };
      ConcreteExpression leftTerm = computeTerm(mulArgs.get(mulArgs.size() - 2), coefficients1, freeCoef1);
      ConcreteExpression rightTerm = computeTerm(mulArgs.get(mulArgs.size() - 1), coefficients2, freeCoef2);
      if (coefficients1.isEmpty() && coefficients2.isEmpty()) {
        freeCoef[0] = freeCoef[0].add(freeCoef1[0].multiply(freeCoef2[0]));
      } else if (coefficients1.isEmpty() || coefficients2.isEmpty()) {
        BigInteger coef = coefficients1.isEmpty() ? freeCoef1[0] : freeCoef2[0];
        for (Map.Entry<Integer, BigInteger> entry : coefficients1.entrySet()) {
          BigInteger newCoef = entry.getValue().multiply(coef);
          coefficients.compute(entry.getKey(), (k,v) -> v == null ? newCoef : v.add(newCoef));
        }
        for (Map.Entry<Integer, BigInteger> entry : coefficients2.entrySet()) {
          BigInteger newCoef = entry.getValue().multiply(coef);
          coefficients.compute(entry.getKey(), (k,v) -> v == null ? newCoef : v.add(newCoef));
        }
        freeCoef[0] = freeCoef[0].add(freeCoef1[0].multiply(freeCoef2[0]));
      } else {
        values.getValues().subList(valuesSize, values.getValues().size()).clear();
        coefficients.compute(values.addValue(expr), (k,v) -> v == null ? BigInteger.ONE : v.add(BigInteger.ONE));
      }
      return factory.app(factory.ref(meta.mulTerm.getRef()), true, leftTerm, rightTerm);
    }

    int index = values.addValue(expr);
    coefficients.compute(index, (k,v) -> v == null ? BigInteger.ONE : v.add(BigInteger.ONE));
    return factory.app(factory.ref(meta.varTerm.getRef()), true, factory.number(index));
  }
}
