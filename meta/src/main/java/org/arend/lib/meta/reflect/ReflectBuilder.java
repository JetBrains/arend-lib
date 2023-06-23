package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.level.*;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.concrete.pattern.*;
import org.arend.ext.core.context.CoreInferenceVariable;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.error.FieldsImplementationError;
import org.arend.ext.error.MissingArgumentsError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;

import java.util.*;
import java.util.function.Function;

public class ReflectBuilder implements ConcreteVisitor<Void, ConcreteExpression>, ConcreteLevelVisitor<Void, ConcreteExpression> {
  private final ConcreteFactory factory;
  private final ExpressionTypechecker typechecker;
  private final StdExtension ext;
  private final Map<ArendRef, Integer> localRefs = new HashMap<>();

  public ReflectBuilder(ExpressionTypechecker typechecker, StdExtension ext, ConcreteFactory factory) {
    this.factory = factory;
    this.typechecker = typechecker;
    this.ext = ext;
  }

  public static ConcreteExpression process(ConcreteExpression expr, ExpressionTypechecker typechecker, StdExtension ext, ConcreteFactory factory) {
    try {
      return expr.accept(new ReflectBuilder(typechecker, ext, factory), null);
    } catch (ReflectionException e) {
      typechecker.getErrorReporter().report(e.error);
      return null;
    }
  }

  public ConcreteExpression makeBool(boolean b) {
    return factory.ref(b ? ext.true_.getRef() : ext.false_.getRef());
  }

  @Override
  public ConcreteExpression visitApp(ConcreteAppExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    boolean isSplice = expr.getFunction() instanceof ConcreteReferenceExpression refExpr && refExpr.getReferent() == ext.spliceRef;
    boolean isQuote = expr.getFunction() instanceof ConcreteReferenceExpression refExpr && refExpr.getReferent() == ext.quoteRef;
    List<? extends ConcreteArgument> arguments = expr.getArguments();
    if ((isSplice || isQuote) && (arguments.isEmpty() || !arguments.get(0).isExplicit())) {
      throw new ReflectionException(new TypecheckingError("Expected an explicit argument", expr.getFunction()));
    }

    ConcreteExpression result = isSplice ? arguments.get(0).getExpression() : isQuote ? factory.app(factory.ref(ext.tcMeta.quoteExpr.getRef()), true, arguments.get(0).getExpression()) : expr.getFunction().accept(this, null);
    for (int i = isSplice || isQuote ? 1 : 0; i < arguments.size(); i++) {
      ConcreteArgument argument = arguments.get(i);
      result = factory.app(factory.ref(ext.tcMeta.appExpr.getRef()), true, result, argument.getExpression().accept(this, null), makeBool(argument.isExplicit()));
    }
    return result;
  }

  public ConcreteExpression listToArray(List<? extends ConcreteExpression> list) {
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

  private ConcreteExpression getLocalVar(ArendRef ref) {
    Integer n = localRefs.get(ref);
    if (n == null) {
      if (typechecker.getFreeBinding(ref) != null) {
        return factory.app(factory.ref(ext.tcMeta.quoteExpr.getRef()), true, factory.ref(ref));
      }
    } else {
      n = localRefs.size() - 1 - n;
    }
    return n == null ? null : factory.app(factory.ref(ext.tcMeta.localVar.getRef()), true, factory.number(n)) ;
  }

  @Override
  public ConcreteExpression visitReference(ConcreteReferenceExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    ArendRef ref = expr.getReferent();
    if (ref == ext.quoteRef || ref == ext.spliceRef) {
      throw new ReflectionException(new MissingArgumentsError(1, expr));
    }

    CoreInferenceVariable infVar = ref.getInferenceVariable();
    if (infVar != null) {
      TypedExpression typedExpr = infVar.computeTyped();
      return factory.app(factory.ref(ext.tcMeta.quoteExpr.getRef()), factory.arg(factory.core(typedExpr.getType().computeTyped()), false), factory.arg(factory.core(typedExpr), true));
    }

    ConcreteExpression var = getLocalVar(ref);
    if (var == null && ref.isLocalRef()) {
      throw new ReflectionException(new UnknownReferenceError(ref, expr));
    }
    return var != null ? var : factory.app(factory.ref(ext.tcMeta.globalVar.getRef()), true, factory.qName(ref), levelsToExpression(expr.getPLevels()), levelsToExpression(expr.getHLevels()));
  }

  @Override
  public ConcreteExpression visitThis(ConcreteThisExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.ref(ext.tcMeta.thisExpr.getRef());
  }

  private void addRef(ArendRef ref) {
    if (ref != null) {
      localRefs.put(ref, localRefs.size());
    }
  }

  private void removeRef(ArendRef ref) {
    if (ref != null) {
      localRefs.remove(ref);
    }
  }

  private <T> T processParameters(List<? extends ConcreteParameter> params, Function<List<ConcreteExpression>, T> body) {
    List<ConcreteExpression> parameters = new ArrayList<>();
    for (ConcreteParameter param : params) {
      ConcreteExpression type = param.getType();
      for (ArendRef ref : param.getRefList()) {
        ConcreteExpression newType = exprToExpression(type);
        parameters.add(factory.tuple(makeBool(param.isExplicit()), refNameToExpr(ref), newType));
        addRef(ref);
      }
    }
    T result = body.apply(parameters);
    for (ConcreteParameter parameter : params) {
      for (ArendRef ref : parameter.getRefList()) {
        removeRef(ref);
      }
    }
    return result;
  }

  private ConcreteExpression processParameters(List<? extends ConcreteParameter> params, ConcreteExpression body, CoreConstructor constructor, ConcreteExpression expr) {
    ConcreteFactory factory = this.factory.withData(expr);
    return processParameters(params, parameters -> {
      ConcreteExpression result = body.accept(this, null);
      for (int i = parameters.size() - 1; i >= 0; i--) {
        result = factory.app(factory.ref(constructor.getRef()), true, parameters.get(i), result);
      }
      return result;
    });
  }

  @Override
  public ConcreteExpression visitLam(ConcreteLamExpression expr, Void params) {
    return processParameters(expr.getParameters(), expr.getBody(), ext.tcMeta.lamExpr, expr);
  }

  @Override
  public ConcreteExpression visitPi(ConcretePiExpression expr, Void params) {
    return processParameters(expr.getParameters(), expr.getCodomain(), ext.tcMeta.piExpr, expr);
  }

  private ConcreteExpression levelToExpression(ConcreteLevel level) {
    return level == null ? factory.ref(ext.nothing.getRef()) : factory.app(factory.ref(ext.just.getRef()), true, level.accept(this, null));
  }

  private ConcreteExpression exprToExpression(ConcreteExpression expr) {
    return expr == null ? factory.ref(ext.nothing.getRef()) : factory.app(factory.ref(ext.just.getRef()), true, expr.accept(this, null));
  }

  @Override
  public ConcreteExpression visitUniverse(ConcreteUniverseExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.universeExpr.getRef()), true, levelToExpression(expr.getPLevel()), levelToExpression(expr.getHLevel()));
  }

  @Override
  public ConcreteExpression visitHole(ConcreteHoleExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.ref(ext.tcMeta.holeExpr.getRef());
  }

  @Override
  public ConcreteExpression visitGoal(ConcreteGoalExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.ref(ext.tcMeta.goalExpr.getRef());
  }

  @Override
  public ConcreteExpression visitTuple(ConcreteTupleExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    List<ConcreteExpression> list = new ArrayList<>();
    for (ConcreteExpression field : expr.getFields()) {
      list.add(field.accept(this, null));
    }
    return factory.app(factory.ref(ext.tcMeta.tupleExpr.getRef()), true, listToArray(list));
  }

  @Override
  public ConcreteExpression visitSigma(ConcreteSigmaExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    List<ConcreteExpression> list = new ArrayList<>();
    for (ConcreteParameter param : expr.getParameters()) {
      if (param.getType() == null) {
        throw new ReflectionException(new TypecheckingError("Parameters in \\Sigma-types must have types", expr));
      }
      for (ArendRef ref : param.getRefList()) {
        list.add(factory.tuple(refNameToExpr(ref), param.getType().accept(this, null)));
        addRef(ref);
      }
    }
    for (ConcreteParameter param : expr.getParameters()) {
      for (ArendRef ref : param.getRefList()) {
        removeRef(ref);
      }
    }
    return factory.app(factory.ref(ext.tcMeta.sigmaExpr.getRef()), true, listToArray(list));
  }

  private ConcreteExpression makePatternInternal(ConcretePattern pattern) {
    ConcreteFactory factory = this.factory.withData(pattern);
    if (pattern instanceof ConcreteNumberPattern numPattern) {
      return factory.app(factory.ref(ext.tcMeta.numberPattern.getRef()), true, makeNumber(numPattern.getNumber()));
    } else if (pattern instanceof ConcreteConstructorPattern conPattern) {
      ArendRef ref = conPattern.getConstructor();
      if (ref == null) {
        throw new ReflectionException(new TypecheckingError("A constructor pattern without constructor", pattern));
      }
      return factory.app(factory.ref(ext.tcMeta.conPattern.getRef()), true, factory.qName(ref), makePatterns(conPattern.getPatterns()));
    } else if (pattern instanceof ConcreteTuplePattern tuplePattern) {
      return factory.app(factory.ref(ext.tcMeta.tuplePattern.getRef()), true, makePatterns(tuplePattern.getPatterns()));
    } else if (pattern instanceof ConcreteReferencePattern refPattern) {
      ConcreteExpression type = exprToExpression(refPattern.getType());
      ArendRef ref = refPattern.getRef();
      addRef(ref);
      return factory.app(factory.ref(ext.tcMeta.namePattern.getRef()), true, refNameToExpr(ref), type);
    } else {
      throw new ReflectionException(new TypecheckingError("Unknown pattern", pattern));
    }
  }

  private ConcreteExpression makePattern(ConcretePattern pattern) {
    ConcreteFactory factory = this.factory.withData(pattern);
    ArendRef ref = pattern.getAsRef();
    ConcreteExpression type = exprToExpression(pattern.getAsRefType());
    ConcreteExpression result = makePatternInternal(pattern);
    addRef(ref);
    return factory.tuple(result, refNameToExpr(ref), type);
  }

  private ConcreteExpression makePatterns(List<? extends ConcretePattern> patterns) {
    List<ConcreteExpression> result = new ArrayList<>();
    for (ConcretePattern pattern : patterns) {
      result.add(makePattern(pattern));
    }
    return listToArray(result);
  }

  private void freePattern(ConcretePattern pattern) {
    if (pattern instanceof ConcreteReferencePattern refPattern) {
      removeRef(refPattern.getRef());
    }
    removeRef(pattern.getAsRef());
    freePatterns(pattern.getPatterns());
  }

  private void freePatterns(List<? extends ConcretePattern> patterns) {
    for (ConcretePattern pattern : patterns) {
      freePattern(pattern);
    }
  }

  @Override
  public ConcreteExpression visitCase(ConcreteCaseExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    List<ConcreteExpression> args = new ArrayList<>();
    for (ConcreteCaseArgument argument : expr.getArguments()) {
      ConcreteExpression argExpr = argument.getExpression();
      ConcreteExpression var = null;
      if (argument.isElim() && argExpr instanceof ConcreteReferenceExpression refExpr) {
        var = getLocalVar(refExpr.getReferent());
        if (var == null) {
          throw new ReflectionException(new UnknownReferenceError(refExpr.getReferent(), refExpr));
        }
      }
      ArendRef asRef = var == null ? argument.getAsRef() : null;
      args.add(factory.tuple(var != null ? factory.app(factory.ref(ext.inr.getRef()), true, var) : factory.app(factory.ref(ext.inl.getRef()), true, factory.tuple(argExpr.accept(this, null), refNameToExpr(asRef))), exprToExpression(argument.getType())));
      addRef(asRef);
    }
    ConcreteExpression resultType = exprToExpression(expr.getResultType());
    ConcreteExpression resultTypeLevel = exprToExpression(expr.getResultTypeLevel());
    for (ConcreteCaseArgument argument : expr.getArguments()) {
      removeRef(argument.getAsRef());
    }

    List<ConcreteExpression> clauses = new ArrayList<>();
    for (ConcreteClause clause : expr.getClauses()) {
      List<ConcreteExpression> result = new ArrayList<>();
      for (ConcretePattern pattern : clause.getPatterns()) {
        result.add(makePattern(pattern));
      }
      ConcreteExpression patterns = listToArray(result);
      clauses.add(factory.tuple(patterns, exprToExpression(clause.getExpression())));
      freePatterns(clause.getPatterns());
    }
    return factory.app(factory.ref(ext.tcMeta.caseExpr.getRef()), true, makeBool(expr.isSCase()), listToArray(args), resultType, resultTypeLevel, listToArray(clauses));
  }

  @Override
  public ConcreteExpression visitEval(ConcreteEvalExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.evalExpr.getRef()), true, makeBool(expr.isPEval()), expr.getExpression().accept(this, null));
  }

  @Override
  public ConcreteExpression visitBox(ConcreteBoxExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.boxExpr.getRef()), true, expr.getExpression().accept(this, null));
  }

  @Override
  public ConcreteExpression visitProj(ConcreteProjExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.projExpr.getRef()), true, expr.getExpression().accept(this, null), factory.number(expr.getField()));
  }

  private ConcreteExpression coclauseToExpression(ConcreteCoclause coclause) {
    ConcreteFactory factory = this.factory.withData(coclause);
    ConcreteExpression impl = coclause.getImplementation();
    if (impl == null) {
      ArendRef classRef = coclause.getClassReference();
      ConcreteCoclauses coclauses = coclause.getSubCoclauses();
      if (classRef == null || coclauses == null) {
        throw new ReflectionException(new FieldsImplementationError(false, null, Collections.singletonList(coclause.getImplementedRef()), coclause));
      }
      impl = factory.newExpr(factory.classExt(factory.ref(classRef), coclauses.getCoclauseList()));
    }
    return factory.tuple(factory.qName(coclause.getImplementedRef()), impl.accept(this, null));
  }

  @Override
  public ConcreteExpression visitClassExt(ConcreteClassExtExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    List<ConcreteExpression> coclauses = new ArrayList<>();
    for (ConcreteCoclause coclause : expr.getCoclauses().getCoclauseList()) {
      coclauses.add(coclauseToExpression(coclause));
    }
    return factory.app(factory.ref(ext.tcMeta.classExtExpr.getRef()), true, expr.getBaseClassExpression().accept(this, null), listToArray(coclauses));
  }

  @Override
  public ConcreteExpression visitNew(ConcreteNewExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.newExpr.getRef()), true, expr.getExpression().accept(this, null));
  }

  @Override
  public ConcreteExpression visitLet(ConcreteLetExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    List<ConcreteExpression> clauses = new ArrayList<>();
    for (ConcreteLetClause clause : expr.getClauses()) {
      ConcreteExpression[] array = processParameters(clause.getParameters(), parameters -> new ConcreteExpression[] { listToArray(parameters), exprToExpression(clause.getResultType()), clause.getTerm().accept(this, null) });
      clauses.add(factory.tuple(makePattern(clause.getPattern()), array[0], array[1], array[2]));
    }
    ConcreteExpression result = factory.app(factory.ref(ext.tcMeta.letExpr.getRef()), true, makeBool(expr.isHave()), makeBool(expr.isStrict()), listToArray(clauses), expr.getExpression().accept(this, null));
    for (ConcreteLetClause clause : expr.getClauses()) {
      freePattern(clause.getPattern());
    }
    return result;
  }

  @Override
  public ConcreteExpression visitNumber(ConcreteNumberExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.numberExpr.getRef()), true, factory.number(expr.getNumber()));
  }

  private ConcreteExpression refNameToExpr(ArendRef ref) {
    return factory.string(ref == null ? "" : ref.getRefName());
  }

  @Override
  public ConcreteExpression visitString(ConcreteStringExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.stringExpr.getRef()), true, factory.string(expr.getUnescapedString()));
  }

  @Override
  public ConcreteExpression visitQName(ConcreteQNameExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.qNameExpr.getRef()), true, factory.qName(expr.getReference()));
  }

  @Override
  public ConcreteExpression visitTyped(ConcreteTypedExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.typedExpr.getRef()), true, expr.getExpression().accept(this, null), expr.getType().accept(this, null));
  }

  @Override
  public ConcreteExpression visitCore(ConcreteCoreExpression expr, Void params) {
    ConcreteFactory factory = this.factory.withData(expr);
    TypedExpression typedExpr = expr.getTypedExpression();
    return factory.app(factory.ref(ext.tcMeta.quoteExpr.getRef()), factory.arg(factory.core(typedExpr.getType().computeTyped()), false), factory.arg(factory.core(typedExpr), true));
  }

  @Override
  public ConcreteExpression visitInf(ConcreteInfLevel expr, Void param) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.ref(ext.tcMeta.infLevel.getRef());
  }

  @Override
  public ConcreteExpression visitLP(ConcreteLPLevel expr, Void param) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.stdLevel.getRef()), true, factory.ref(ext.tcMeta.pLevel.getRef()));
  }

  @Override
  public ConcreteExpression visitLH(ConcreteLHLevel expr, Void param) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.stdLevel.getRef()), true, factory.ref(ext.tcMeta.pLevel.getRef()));
  }

  private ConcreteExpression makeNumber(int number) {
    ConcreteExpression expr = factory.number(number < 0 ? -number : number);
    return factory.app(factory.ref(number < 0 ? ext.prelude.getNeg().getRef() : ext.prelude.getPos().getRef()), true, expr);
  }

  @Override
  public ConcreteExpression visitNumber(ConcreteNumberLevel expr, Void param) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.numberLevel.getRef()), true, makeNumber(expr.getNumber()));
  }

  @Override
  public ConcreteExpression visitVar(ConcreteVarLevel expr, Void param) {
    ConcreteFactory factory = this.factory.withData(expr);
    ArendRef ref = expr.getReferent();
    if (ref.isInferenceRef()) {
      return factory.app(factory.ref(ext.tcMeta.varLevel.getRef()), true, factory.qName(ref));
    }

    int index = typechecker.getLevelVariableIndex(ref);
    if (index < 0) {
      throw new ReflectionException(new UnknownReferenceError(ref, expr));
    }
    return factory.app(factory.ref(ext.tcMeta.varLevel.getRef()), true, factory.number(index), factory.ref(ref.getRefKind() == ArendRef.RefKind.PLEVEL ? ext.tcMeta.pLevel.getRef() : ext.tcMeta.hLevel.getRef()));
  }

  @Override
  public ConcreteExpression visitSuc(ConcreteSucLevel expr, Void param) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.sucLevel.getRef()), true, expr.getExpression().accept(this, null));
  }

  @Override
  public ConcreteExpression visitMax(ConcreteMaxLevel expr, Void param) {
    ConcreteFactory factory = this.factory.withData(expr);
    return factory.app(factory.ref(ext.tcMeta.maxLevel.getRef()), true, expr.getLeft().accept(this, null), expr.getRight().accept(this, null));
  }
}
