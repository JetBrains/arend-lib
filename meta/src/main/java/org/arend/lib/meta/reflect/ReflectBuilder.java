package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.level.*;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.lib.StdExtension;

import java.util.*;

public class ReflectBuilder implements ConcreteVisitor<Void, ConcreteExpression>, ConcreteLevelVisitor<Void, ConcreteExpression> {
  private final ConcreteFactory factory;
  private final ExpressionTypechecker typechecker;
  private final StdExtension ext;
  private final ConcreteExpression marker;
  private final Map<ArendRef, Integer> localRefs = new HashMap<>();

  public ReflectBuilder(ExpressionTypechecker typechecker, StdExtension ext, ConcreteExpression marker) {
    this.factory = ext.factory.withData(marker);
    this.typechecker = typechecker;
    this.ext = ext;
    this.marker = marker;
  }

  private ConcreteExpression makeBool(boolean b) {
    return factory.ref(b ? ext.true_.getRef() : ext.false_.getRef());
  }

  @Override
  public ConcreteExpression visitApp(ConcreteAppExpression expr, Void params) {
    ConcreteExpression result = expr.getFunction().accept(this, null);
    for (ConcreteArgument argument : expr.getArguments()) {
      result = factory.app(factory.ref(ext.tcMeta.appExpr.getRef()), true, result, argument.getExpression().accept(this, null), makeBool(argument.isExplicit()));
    }
    return result;
  }

  private ConcreteExpression listToArray(List<? extends ConcreteExpression> list) {
    ConcreteExpression result = factory.ref(ext.prelude.getEmptyArray().getRef());
    for (int i = list.size() - 1; i >= 0; i--) {
      result = factory.app(factory.ref(ext.prelude.getArrayCons().getRef()), true, list.get(i), result);
    }
    return result;
  }

  private ConcreteExpression levelsToExpression(List<? extends ConcreteLevel> levels) {
    if (levels == null) {
      return factory.ref(ext.nothing.getRef());
    }

    List<ConcreteExpression> list = new ArrayList<>(levels.size());
    for (ConcreteLevel level : levels) {
      list.add(level.accept(this, null));
    }
    return factory.app(factory.ref(ext.just.getRef()), true, listToArray(list));
  }

  @Override
  public ConcreteExpression visitReference(ConcreteReferenceExpression expr, Void params) {
    ArendRef ref = expr.getReferent();
    Integer n = localRefs.get(ref);
    if (n == null) {
      CoreBinding binding = typechecker.getFreeBinding(ref);
      if (binding != null) {
        List<CoreBinding> context = typechecker.getFreeBindingsList();
        int index = context.lastIndexOf(binding);
        if (index >= 0) {
          n = context.size() - 1 - index;
        }
      }
    } else {
      n = localRefs.size() - 1 - n;
    }
    return n != null ? factory.app(factory.ref(ext.tcMeta.localVar.getRef()), true, factory.number(n)) : factory.app(factory.ref(ext.tcMeta.globalVar.getRef()), true, factory.qName(ref), levelsToExpression(expr.getPLevels()), levelsToExpression(expr.getHLevels()));
  }

  @Override
  public ConcreteExpression visitThis(ConcreteThisExpression expr, Void params) {
    return factory.ref(ext.tcMeta.thisExpr.getRef());
  }

  private void addRef(ArendRef ref) {
    if (ref != null) {
      localRefs.put(ref, localRefs.size());
    }
  }

  private ConcreteExpression processParameters(List<? extends ConcreteParameter> params, ConcreteExpression body, CoreConstructor constructor) {
    List<ConcreteExpression> parameters = new ArrayList<>();
    for (int i = params.size() - 1; i >= 0; i--) {
      ConcreteParameter param = params.get(i);
      List<? extends ArendRef> refList = param.getRefList();
      ConcreteExpression type = param.getType();
      for (int j = refList.size() - 1; j >= 0; j--) {
        ArendRef ref = refList.get(j);
        parameters.add(factory.tuple(makeBool(param.isExplicit()), makeBool(ref != null), type == null ? factory.ref(ext.nothing.getRef()) : factory.app(factory.ref(ext.just.getRef()), true, type.accept(this, null))));
        addRef(ref);
      }
    }
    ConcreteExpression result = body.accept(this, null);
    for (int i = parameters.size() - 1; i >= 0; i--) {
      result = factory.app(factory.ref(constructor.getRef()), true, parameters.get(i), result);
    }
    for (ConcreteParameter parameter : params) {
      for (ArendRef ref : parameter.getRefList()) {
        if (ref != null) {
          localRefs.remove(ref);
        }
      }
    }
    return result;
  }

  @Override
  public ConcreteExpression visitLam(ConcreteLamExpression expr, Void params) {
    return processParameters(expr.getParameters(), expr.getBody(), ext.tcMeta.lamExpr);
  }

  @Override
  public ConcreteExpression visitPi(ConcretePiExpression expr, Void params) {
    return processParameters(expr.getParameters(), expr.getCodomain(), ext.tcMeta.piExpr);
  }

  private ConcreteExpression levelToExpression(ConcreteLevel level) {
    return level == null ? factory.ref(ext.nothing.getRef()) : factory.app(factory.ref(ext.just.getRef()), true, level.accept(this, null));
  }

  @Override
  public ConcreteExpression visitUniverse(ConcreteUniverseExpression expr, Void params) {
    return factory.app(factory.ref(ext.tcMeta.universeExpr.getRef()), true, levelToExpression(expr.getPLevel()), levelToExpression(expr.getHLevel()));
  }

  @Override
  public ConcreteExpression visitHole(ConcreteHoleExpression expr, Void params) {
    return factory.ref(ext.tcMeta.holeExpr.getRef());
  }

  @Override
  public ConcreteExpression visitGoal(ConcreteGoalExpression expr, Void params) {
    return factory.ref(ext.tcMeta.goalExpr.getRef());
  }

  @Override
  public ConcreteExpression visitTuple(ConcreteTupleExpression expr, Void params) {
    List<ConcreteExpression> list = new ArrayList<>();
    for (ConcreteExpression field : expr.getFields()) {
      list.add(field.accept(this, null));
    }
    return factory.app(factory.ref(ext.tcMeta.tupleExpr.getRef()), true, listToArray(list));
  }

  @Override
  public ConcreteExpression visitSigma(ConcreteSigmaExpression expr, Void params) {
    List<ConcreteExpression> list = new ArrayList<>();
    for (ConcreteParameter param : expr.getParameters()) {
      if (param.getType() == null) {
        typechecker.getErrorReporter().report(new TypecheckingError("Parameters in \\Sigma-types must have types", marker));
        return null;
      }
      ConcreteExpression type = param.getType().accept(this, null);
      for (ArendRef ref : param.getRefList()) {
        list.add(factory.tuple(makeBool(ref != null), type));
        addRef(ref);
      }
    }
    for (ConcreteParameter param : expr.getParameters()) {
      for (ArendRef ref : param.getRefList()) {
        localRefs.remove(ref);
      }
    }
    return factory.app(factory.ref(ext.tcMeta.sigmaExpr.getRef()), true, listToArray(list));
  }

  @Override
  public ConcreteExpression visitCase(ConcreteCaseExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitEval(ConcreteEvalExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitBox(ConcreteBoxExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitProj(ConcreteProjExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitClassExt(ConcreteClassExtExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitNew(ConcreteNewExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitLet(ConcreteLetExpression expr, Void params) {
    return null;
  }

  @Override
  public ConcreteExpression visitNumber(ConcreteNumberExpression expr, Void params) {
    return factory.app(factory.ref(ext.tcMeta.numberExpr.getRef()), true, factory.number(expr.getNumber()));
  }

  @Override
  public ConcreteExpression visitString(ConcreteStringExpression expr, Void params) {
    return factory.app(factory.ref(ext.tcMeta.stringExpr.getRef()), true, factory.string(expr.getUnescapedString()));
  }

  @Override
  public ConcreteExpression visitQName(ConcreteQNameExpression expr, Void params) {
    return factory.app(factory.ref(ext.tcMeta.qNameExpr.getRef()), true, factory.qName(expr.getReference()));
  }

  @Override
  public ConcreteExpression visitTyped(ConcreteTypedExpression expr, Void params) {
    return factory.app(factory.ref(ext.tcMeta.typedExpr.getRef()), true, expr.getExpression().accept(this, null), expr.getType().accept(this, null));
  }

  @Override
  public ConcreteExpression visitInf(ConcreteInfLevel expr, Void param) {
    return factory.ref(ext.tcMeta.infLevel.getRef());
  }

  @Override
  public ConcreteExpression visitLP(ConcreteLPLevel expr, Void param) {
    return factory.app(factory.ref(ext.tcMeta.stdLevel.getRef()), true, factory.ref(ext.tcMeta.pLevel.getRef()));
  }

  @Override
  public ConcreteExpression visitLH(ConcreteLHLevel expr, Void param) {
    return factory.app(factory.ref(ext.tcMeta.stdLevel.getRef()), true, factory.ref(ext.tcMeta.pLevel.getRef()));
  }

  @Override
  public ConcreteExpression visitNumber(ConcreteNumberLevel expr, Void param) {
    return factory.app(factory.ref(ext.tcMeta.numberLevel.getRef()), true, factory.number(expr.getNumber()));
  }

  @Override
  public ConcreteExpression visitVar(ConcreteVarLevel expr, Void param) {
    int pIndex = typechecker.getLevelVariables(true).indexOf(expr.getReferent());
    int hIndex = pIndex == -1 ? typechecker.getLevelVariables(false).indexOf(expr.getReferent()) : -1;
    if (pIndex < 0 && hIndex < 0) {
      typechecker.getErrorReporter().report(new UnknownReferenceError(expr.getReferent(), marker));
      return null;
    }
    return factory.app(factory.ref(ext.tcMeta.varLevel.getRef()), true, factory.number(pIndex >= 0 ? pIndex : hIndex), factory.ref(pIndex >= 0 ? ext.tcMeta.pLevel.getRef() : ext.tcMeta.hLevel.getRef()));
  }

  @Override
  public ConcreteExpression visitSuc(ConcreteSucLevel expr, Void param) {
    return factory.app(factory.ref(ext.tcMeta.sucLevel.getRef()), true, expr.getExpression().accept(this, null));
  }

  @Override
  public ConcreteExpression visitMax(ConcreteMaxLevel expr, Void param) {
    return factory.app(factory.ref(ext.tcMeta.maxLevel.getRef()), true, expr.getLeft().accept(this, null), expr.getRight().accept(this, null));
  }
}
