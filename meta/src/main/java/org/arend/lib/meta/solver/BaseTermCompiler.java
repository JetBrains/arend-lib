package org.arend.lib.meta.solver;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.equation.EquationMeta;
import org.arend.lib.meta.equation.binop_matcher.DefinitionFunctionMatcher;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.Set;

public abstract class BaseTermCompiler {
  protected final FunctionMatcher zroMatcher;
  protected final FunctionMatcher ideMatcher;
  protected final FunctionMatcher mulMatcher;
  protected final FunctionMatcher addMatcher;
  protected final FunctionMatcher natCoefMatcher;
  protected final FunctionMatcher negativeMatcher;
  public final FunctionMatcher minusMatcher;
  protected final FunctionMatcher ratAlgebraMatcher;
  protected final ConcreteFactory factory;
  protected final Values<CoreExpression> values;
  protected final RingKind kind;
  protected final boolean toInt;
  protected final boolean toRat;
  protected final BaseTermCompiler subTermCompiler;
  protected final ExpressionTypechecker typechecker;
  public final Set<Integer> positiveVars;
  protected final CoreExpression instance;
  protected final ConcreteSourceNode marker;
  protected final EquationMeta meta;

  protected BaseTermCompiler(CoreClassCallExpression classCall, boolean isRing, boolean isLattice, TypedExpression instance, RingKind kind, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values, Set<Integer> positiveVars, boolean toInt, boolean toRat) {
    meta = ext.equationMeta;
    factory = ext.factory.withData(marker);
    zroMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, isLattice ? meta.bottom : meta.ext.zro, typechecker, factory, marker, ext, 0);
    ideMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, isLattice ? meta.top : ext.ide, typechecker, factory, marker, ext, 0);
    addMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, isLattice ? meta.join : meta.plus, typechecker, factory, marker, ext, 2);
    mulMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, isLattice ? meta.meet : meta.mul, typechecker, factory, marker, ext, 2);
    natCoefMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, meta.natCoef, typechecker, factory, marker, ext, 1);
    negativeMatcher = isRing ? FunctionMatcher.makeFieldMatcher(classCall, instance, meta.negative, typechecker, factory, marker, ext, 1) : null;
    ratAlgebraMatcher = kind == RingKind.RAT_ALG ? FunctionMatcher.makeFieldMatcher(classCall, instance, meta.ext.linearSolverMeta.coefMap, typechecker, factory, marker, ext, 1) : null;
    minusMatcher = toInt ? new DefinitionFunctionMatcher(ext.prelude.getMinus(), 2) : null;
    this.values = values;
    this.kind = kind;
    BaseTermCompiler subTermCompiler = null;
    if (kind == RingKind.INT || kind == RingKind.RAT) {
      CoreFunctionDefinition subInstance = kind == RingKind.INT ? meta.NatSemiring : meta.IntRing;
      TypedExpression typed = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(factory.ref(subInstance.getRef()), null));
      if (typed != null) {
        subTermCompiler = newInstance((CoreClassCallExpression) subInstance.getResultType(), typed, kind == RingKind.INT ? RingKind.NAT : RingKind.INT, ext, typechecker, marker, values, positiveVars, kind == RingKind.INT, kind == RingKind.RAT);
      }
    }
    this.toInt = toInt;
    this.toRat = toRat;
    this.subTermCompiler = subTermCompiler;
    this.typechecker = typechecker;
    this.positiveVars = positiveVars;
    this.instance = instance.getExpression();
    this.marker = marker;
  }

  protected BaseTermCompiler(CoreClassCallExpression classCall, boolean isRing, boolean isLattice, TypedExpression instance, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values) {
    this(classCall, isRing, isLattice, instance, getTermCompilerKind(instance.getExpression(), ext.equationMeta), ext, typechecker, marker, values, new HashSet<>(), false, false);
  }

  protected abstract BaseTermCompiler newInstance(CoreClassCallExpression classCall, TypedExpression instance, RingKind kind, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker, Values<CoreExpression> values, Set<Integer> positiveVars, boolean toInt, boolean toRat);

  public static RingKind getTermCompilerKind(CoreExpression instance, EquationMeta meta) {
    CoreExpression instanceNorm = instance.normalize(NormalizationMode.WHNF);
    CoreFunctionDefinition instanceDef = instanceNorm instanceof CoreFunCallExpression ? ((CoreFunCallExpression) instanceNorm).getDefinition() : null;
    RingKind kind = instanceDef == meta.NatSemiring ? RingKind.NAT : instanceDef == meta.IntRing ? RingKind.INT : instanceDef == meta.RatField ? RingKind.RAT : RingKind.NONE;
    if (kind != RingKind.NONE) return kind;
    CoreExpression type = instanceNorm.computeType().normalize(NormalizationMode.WHNF);
    if (type instanceof CoreClassCallExpression classCall && classCall.getDefinition().isSubClassOf(meta.ext.linearSolverMeta.OrderedAAlgebra)) {
      CoreExpression ringImpl = classCall.getAbsImplementationHere(meta.ext.linearSolverMeta.moduleRing);
      if (ringImpl != null) {
        ringImpl = ringImpl.normalize(NormalizationMode.WHNF);
        if (ringImpl instanceof CoreFunCallExpression funCall && funCall.getDefinition() == meta.RatField) {
          return RingKind.RAT_ALG;
        }
      }
    }
    return RingKind.NONE;
  }

  protected Pair<Boolean, CoreExpression> checkInt(CoreExpression expr) {
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

  protected BigInteger getInt(CoreExpression expr) {
    Pair<Boolean, CoreExpression> pair = checkInt(expr);
    if (pair == null) return null;
    CoreExpression arg = pair.proj2.normalize(NormalizationMode.WHNF);
    if (!(arg instanceof CoreIntegerExpression)) return null;
    BigInteger number = ((CoreIntegerExpression) arg).getBigInteger();
    return pair.proj1 ? number.negate() : number;
  }
}
