package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.expr.CoreIntegerExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.meta.equation.binop_matcher.DefinitionFunctionMatcher;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;
import org.arend.lib.ring.Monomial;
import org.arend.lib.util.CountingSort;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.math.BigInteger;
import java.util.*;

import static java.util.Collections.singletonList;

public class RingSolver extends BaseEqualitySolver {
  private final boolean isRing;
  private final boolean isCommutative;
  private final FunctionMatcher zroMatcher;
  private final FunctionMatcher ideMatcher;
  private final FunctionMatcher mulMatcher;
  private final FunctionMatcher addMatcher;
  private final FunctionMatcher natCoefMatcher;
  private final FunctionMatcher intCoefMatcher;
  private final FunctionMatcher negativeMatcher;
  private CompiledTerm lastCompiled;
  private TypedExpression lastTerm;

  protected RingSolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr, CoreFunCallExpression equality, TypedExpression instance, CoreClassCallExpression classCall) {
    super(meta, typechecker, factory, refExpr, instance);
    this.equality = equality;
    isRing = classCall.getDefinition().isSubClassOf(meta.Ring);
    isCommutative = classCall.getDefinition().isSubClassOf(meta.CMonoid);
    zroMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.zro, typechecker, factory, refExpr, meta.ext, 0);
    ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.ide, typechecker, factory, refExpr, meta.ext, 0);
    mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.mul, typechecker, factory, refExpr, meta.ext, 2);
    addMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.plus, typechecker, factory, refExpr, meta.ext, 2);
    natCoefMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.natCoef, typechecker, factory, refExpr, meta.ext, 1);
    intCoefMatcher = isRing ? new DefinitionFunctionMatcher(meta.intCoef, 1) : null;
    negativeMatcher = isRing ? FunctionMatcher.makeFieldMatcher(classCall, instance, meta.negative, typechecker, factory, refExpr, meta.ext, 1) : null;
  }

  @Override
  protected ConcreteExpression getDefaultValue() {
    return factory.ref(meta.ide.getRef());
  }

  @Override
  protected ConcreteExpression getDataClass(ConcreteExpression instanceArg, ConcreteExpression dataArg) {
    ConcreteExpression data = factory.ref((isRing ? (isCommutative ? meta.CRingData : meta.RingData) : (isCommutative ? meta.CSemiringData : meta.SemiringData)).getRef());
    return factory.classExt(data, Arrays.asList(factory.implementation(meta.RDataCarrier.getRef(), instanceArg), factory.implementation(meta.DataFunction.getRef(), dataArg)));
  }

  private static class CompiledTerm {
    final ConcreteExpression concrete;
    final List<Monomial> nf;

    private CompiledTerm(ConcreteExpression concrete, List<Monomial> nf) {
      this.concrete = concrete;
      this.nf = nf;
    }
  }

  private CompiledTerm compileTerm(CoreExpression expression) {
    List<Monomial> nf = new ArrayList<>();
    return new CompiledTerm(computeTerm(expression, nf), nf);
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
        List<Monomial> nf1 = new ArrayList<>();
        List<ConcreteExpression> cArgs = Collections.singletonList(computeTerm(negativeArgs.get(0), nf1));
        Monomial.negate(nf1, nf);
        return factory.app(factory.ref(meta.negativeTerm.getRef()), true, cArgs);
      }
    }

    List<CoreExpression> coefArgs = isRing ? intCoefMatcher.match(expr) : null;
    if (coefArgs == null) {
      coefArgs = natCoefMatcher.match(expr);
    }
    if (coefArgs != null) {
      CoreExpression arg = coefArgs.get(0).normalize(NormalizationMode.WHNF);
      if (arg instanceof CoreIntegerExpression) {
        BigInteger coef = ((CoreIntegerExpression) arg).getBigInteger();
        nf.add(new Monomial(coef, Collections.emptyList()));
        return factory.app(factory.ref(meta.coefTerm.getRef()), true, Collections.singletonList(factory.number(coef)));
      }
    }

    int index = values.addValue(expr);
    nf.add(new Monomial(BigInteger.ONE, Collections.singletonList(index)));
    return factory.app(factory.ref(meta.varTerm.getRef()), true, singletonList(factory.number(index)));
  }

  @Override
  public ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter) {
    CompiledTerm term1 = lastTerm == leftExpr ? lastCompiled : compileTerm(leftExpr.getExpression());
    CompiledTerm term2 = compileTerm(rightExpr.getExpression());
    lastTerm = rightExpr;
    lastCompiled = term2;

    if (isCommutative) {
      for (int i = 0; i < term1.nf.size(); i++) {
        term1.nf.set(i, new Monomial(term1.nf.get(i).coefficient, CountingSort.sort(term1.nf.get(i).elements)));
      }
      for (int i = 0; i < term2.nf.size(); i++) {
        term2.nf.set(i, new Monomial(term2.nf.get(i).coefficient, CountingSort.sort(term2.nf.get(i).elements)));
      }
    }
    Collections.sort(term1.nf);
    Collections.sort(term2.nf);
    if (!Monomial.collapse(term1.nf).equals(Monomial.collapse(term2.nf))) {
      return null;
    }

    return factory.appBuilder(factory.ref((isRing ? (isCommutative ? meta.commRingTermsEq : meta.ringTermsEq) : (isCommutative ? meta.commSemiringTermsEq : meta.semiringTermsEq)).getRef()))
      .app(factory.ref(dataRef), false)
      .app(term1.concrete)
      .app(term2.concrete)
      .app(factory.ref(meta.ext.prelude.getIdp().getRef()))
      .build();
  }
}
