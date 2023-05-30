package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.*;
import org.arend.ext.concrete.expr.ConcreteCaseArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.concrete.level.ConcreteLevel;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.util.Pair;
import org.arend.lib.util.Maybe;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Function;

public class TypecheckBuilder {
  private final TypecheckMeta meta;
  private final ConcreteFactory factory;
  private final ExpressionTypechecker typechecker;
  private final ErrorReporter errorReporter;
  private final ConcreteExpression marker;
  private final List<ArendRef> localRefs = new ArrayList<>();

  public TypecheckBuilder(TypecheckMeta meta, ConcreteFactory factory, ExpressionTypechecker typechecker, ConcreteExpression marker) {
    this.meta = meta;
    this.factory = factory;
    this.typechecker = typechecker;
    errorReporter = typechecker.getErrorReporter();
    this.marker = marker;
  }

  private Integer getSmallInteger(CoreExpression expr) {
    BigInteger n = getInteger(expr);
    if (n == null) return null;
    try {
      return n.intValueExact();
    } catch (ArithmeticException e) {
      TypecheckBuildError.report(errorReporter, "Invalid expression. Expected a small integer.", expr, marker);
      return null;
    }
  }

  private BigInteger getInteger(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreIntegerExpression) {
      return ((CoreIntegerExpression) expr).getBigInteger();
    } else {
      TypecheckBuildError.report(errorReporter, "Expected an integer", expr, marker);
      return null;
    }
  }

  private String getString(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreStringExpression) {
      return ((CoreStringExpression) expr).getString();
    } else {
      TypecheckBuildError.report(errorReporter, "Expected a string", expr, marker);
      return null;
    }
  }

  private ArendRef getQName(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreQNameExpression) {
      return ((CoreQNameExpression) expr).getRef();
    } else {
      TypecheckBuildError.report(errorReporter, "Expected a QName", expr, marker);
      return null;
    }
  }

  private ArendRef getVarRef(CoreExpression expr, LevelType levelType) {
    Integer n = getSmallInteger(expr);
    if (n == null) return null;
    ArendRef ref = typechecker.getLevelVariable(n, levelType == LevelType.PLEVEL);
    if (ref == null) {
      List<? extends ArendRef> refs = typechecker.getLevelVariables(levelType == LevelType.PLEVEL);
      errorReporter.report(new TypecheckingError("Index too large: " + n + ", number of variables: " + refs.size(), marker));
      return null;
    }
    return ref;
  }

  private ConcreteReferenceExpression getLocalRef(CoreExpression expr) {
    Integer n = getSmallInteger(expr);
    if (n == null) return null;
    if (n >= localRefs.size()) {
      int k = n - localRefs.size();
      List<ArendRef> context = typechecker.getFreeReferencesList();
      if (k >= context.size()) {
        errorReporter.report(new TypecheckingError("Index too large: " + n + ", number of variables: " + (localRefs.size() + context.size()), marker));
        return null;
      }
      ArendRef binding = context.get(context.size() - 1 - k);
      ArendRef thisRef = typechecker.getThisReference();
      if (thisRef != null && binding == thisRef) {
        errorReporter.report(new TypecheckingError("A reference to \\this binding", marker));
        return null;
      }
      return factory.ref(binding);
    }
    return factory.ref(localRefs.get(localRefs.size() - 1 - n));
  }

  private ArendRef addRef() {
    ArendRef ref = factory.local("_x" + localRefs.size());
    localRefs.add(ref);
    return ref;
  }

  public ConcreteExpression process(CoreExpression expression) {
    expression = expression.normalize(NormalizationMode.WHNF);
    if (expression instanceof CoreConCallExpression) {
      return processConCall((CoreConCallExpression) expression);
    } else {
      TypecheckBuildError.report(errorReporter, expression, marker);
      return null;
    }
  }

  private <T> List<T> processArray(CoreExpression expr, Function<CoreExpression, T> elementProcessor) {
    List<? extends CoreExpression> elements = expr.getArrayElements();
    if (elements == null) {
      TypecheckBuildError.report(errorReporter, "Invalid expression. Expected an array.", expr, marker);
      return null;
    }

    List<T> result = new ArrayList<>(elements.size());
    for (CoreExpression element : elements) {
      T t = elementProcessor.apply(element);
      if (t == null) return null;
      result.add(t);
    }
    return result;
  }

  private <T> Maybe<T> processMaybe(CoreExpression expr, Function<CoreExpression, T> elementProcessor) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression conCall) {
      CoreConstructor con = conCall.getDefinition();
      if (con == meta.ext.nothing) {
        return new Maybe<>(null);
      } else if (con == meta.ext.just) {
        T t = elementProcessor.apply(conCall.getDefCallArguments().get(0));
        return t == null ? null : new Maybe<>(t);
      }
    }
    TypecheckBuildError.report(errorReporter, "Invalid expression. Expected an array.", expr, marker);
    return null;
  }

  private Boolean processBool(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression conCall) {
      if (conCall.getDefinition() == meta.ext.true_) {
        return true;
      } else if (conCall.getDefinition() == meta.ext.false_) {
        return false;
      }
    }

    TypecheckBuildError.report(errorReporter, "Invalid expression. Expected a boolean.", expr, marker);
    return null;
  }

  private List<? extends CoreExpression> processTuple(CoreExpression expr, int size) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreTupleExpression tuple && tuple.getFields().size() == size) {
      return tuple.getFields();
    } else {
      TypecheckBuildError.report(errorReporter, "Invalid expression. Expected a tuple with " + size + " fields.", expr, marker);
      return null;
    }
  }

  private ConcreteParameter processParameter(CoreExpression expr) {
    List<? extends CoreExpression> fields = processTuple(expr, 3);
    if (fields == null) return null;
    Boolean isExplicit = processBool(fields.get(0));
    Boolean withVar = processBool(fields.get(1));
    Maybe<ConcreteExpression> type = processMaybe(fields.get(2), this::process);
    return isExplicit == null || withVar == null || type == null ? null : withVar ? (type.just == null ? factory.param(isExplicit, addRef()) : factory.param(isExplicit, Collections.singletonList(addRef()), type.just)) : (type.just == null ? factory.param(isExplicit, (ArendRef) null) : factory.param(isExplicit, type.just));
  }

  private void removeVars(int size) {
    localRefs.subList(size, localRefs.size()).clear();
  }

  private ConcreteLetClause processLetClause(CoreExpression expr) {
    List<? extends CoreExpression> fields = processTuple(expr, 4);
    if (fields == null) return null;
    int size = localRefs.size();
    List<ConcreteParameter> parameters = processArray(fields.get(1), this::processParameter);
    Maybe<ConcreteExpression> type = processMaybe(fields.get(2), this::process);
    ConcreteExpression term = process(fields.get(3));
    removeVars(size);
    ConcretePattern pattern = processPattern(fields.get(0));
    return pattern == null || parameters == null || type == null || term == null ? null : factory.letClause(pattern, parameters, type.just, term);
  }

  private ConcreteLevel processLevel(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression) {
      return processLevelConCall((CoreConCallExpression) expr);
    } else {
      TypecheckBuildError.report(errorReporter, expr, marker);
      return null;
    }
  }

  private ConcretePattern processPattern(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression) {
      return processPatternConCall((CoreConCallExpression) expr);
    } else {
      TypecheckBuildError.report(errorReporter, expr, marker);
      return null;
    }
  }

  private ConcretePattern processPatternConCall(CoreConCallExpression expr) {
    CoreConstructor constructor = expr.getDefinition();
    if (constructor == meta.tuplePattern) {
      List<ConcretePattern> patterns = processArray(expr.getDefCallArguments().get(0), this::processPattern);
      return patterns == null ? null : factory.tuplePattern(patterns);
    } else if (constructor == meta.namePattern) {
      Maybe<ConcreteExpression> type = processMaybe(expr.getDefCallArguments().get(1), this::process);
      if (type == null) return null;
      Boolean withVar = processBool(expr.getDefCallArguments().get(0));
      if (withVar == null) return null;
      ArendRef ref = withVar ? addRef() : null;
      return factory.refPattern(ref, type.just);
    } else if (constructor == meta.numberPattern) {
      Integer n = getSmallInteger(expr.getDefCallArguments().get(0));
      return n == null ? null : factory.numberPattern(n);
    } else if (constructor == meta.conPattern) {
      ArendRef ref = getQName(expr.getDefCallArguments().get(0));
      if (ref != null && ref.isLocalRef()) {
        TypecheckBuildError.report(errorReporter, "Expected a constructor", expr.getDefCallArguments().get(0), marker);
        return null;
      }
      List<ConcretePattern> patterns = processArray(expr.getDefCallArguments().get(1), this::processPattern);
      return ref == null || patterns == null ? null : factory.conPattern(ref, patterns);
    } else {
      TypecheckBuildError.report(errorReporter, expr, marker);
      return null;
    }
  }

  private enum LevelType { PLEVEL, HLEVEL }

  private LevelType processLevelType(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression) {
      CoreConstructor con = ((CoreConCallExpression) expr).getDefinition();
      if (con == meta.pLevel) {
        return LevelType.PLEVEL;
      } else if (con == meta.hLevel) {
        return LevelType.HLEVEL;
      }
    }

    TypecheckBuildError.report(errorReporter, expr, marker);
    return null;
  }

  private ConcreteLevel processLevelConCall(CoreConCallExpression expr) {
    CoreConstructor constructor = expr.getDefinition();
    if (constructor == meta.stdLevel) {
      LevelType type = processLevelType(expr.getDefCallArguments().get(0));
      return type == LevelType.PLEVEL ? factory.lp() : type == LevelType.HLEVEL ? factory.lh() : null;
    } else if (constructor == meta.maxLevel) {
      ConcreteLevel level1 = processLevel(expr.getDefCallArguments().get(0));
      ConcreteLevel level2 = processLevel(expr.getDefCallArguments().get(1));
      return level1 == null || level2 == null ? null : factory.maxLevel(level1, level2);
    } else if (constructor == meta.sucLevel) {
      ConcreteLevel level = processLevel(expr.getDefCallArguments().get(0));
      return level == null ? null : factory.sucLevel(level);
    } else if (constructor == meta.numberLevel) {
      Integer n = getSmallInteger(expr.getDefCallArguments().get(0));
      return n == null ? null : factory.numLevel(n);
    } else if (constructor == meta.infLevel) {
      return factory.inf();
    } else if (constructor == meta.varLevel) {
      LevelType type = processLevelType(expr.getDefCallArguments().get(1));
      if (type == null) return null;
      ArendRef ref = getVarRef(expr.getDefCallArguments().get(0), type);
      return ref == null ? null : factory.varLevel(ref);
    } else {
      TypecheckBuildError.report(errorReporter, expr, marker);
      return null;
    }
  }

  private ConcreteExpression processConCall(CoreConCallExpression expr) {
    CoreConstructor constructor = expr.getDefinition();
    if (constructor == meta.thisExpr) {
      return factory.thisExpr(typechecker.getThisReference());
    } else if (constructor == meta.sigmaExpr) {
      int size = localRefs.size();
      List<ConcreteParameter> parameters = processArray(expr.getDefCallArguments().get(0), e -> {
        List<? extends CoreExpression> fields = processTuple(e, 2);
        if (fields == null) return null;
        Boolean withVar = processBool(fields.get(0));
        ConcreteExpression type = process(fields.get(1));
        return withVar == null || type == null ? null : factory.param(true, Collections.singletonList(withVar ? addRef() : null), type);
      });
      removeVars(size);
      return parameters == null ? null : factory.sigma(parameters);
    } else if (constructor == meta.holeExpr) {
      return factory.hole();
    } else if (constructor == meta.universeExpr) {
      Maybe<ConcreteLevel> pLevel = processMaybe(expr.getDefCallArguments().get(0), this::processLevel);
      Maybe<ConcreteLevel> hLevel = processMaybe(expr.getDefCallArguments().get(1), this::processLevel);
      return pLevel == null || hLevel == null ? null : factory.universe(pLevel.just, hLevel.just);
    } else if (constructor == meta.tupleExpr) {
      List<ConcreteExpression> fields = processArray(expr.getDefCallArguments().get(0), this::process);
      return fields == null ? null : factory.tuple(fields);
    } else if (constructor == meta.classExtExpr) {
      ConcreteExpression body = process(expr.getDefCallArguments().get(0));
      List<ConcreteClassElement> elements = processArray(expr.getDefCallArguments().get(1), e -> {
        List<? extends CoreExpression> fields = processTuple(e, 2);
        if (fields == null) return null;
        ArendRef ref = getQName(fields.get(0));
        if (ref != null && ref.isLocalRef()) {
          TypecheckBuildError.report(errorReporter, "Expected a field", fields.get(0), marker);
          return null;
        }
        ConcreteExpression impl = process(fields.get(1));
        return ref == null || impl == null ? null : factory.implementation(ref, impl);
      });
      if (body == null || elements == null) return null;
      return factory.classExt(body, elements);
    } else if (constructor == meta.newExpr) {
      ConcreteExpression subExpr = process(expr.getDefCallArguments().get(0));
      return subExpr == null ? null : factory.newExpr(subExpr);
    } else if (constructor == meta.evalExpr) {
      Boolean isPEval = processBool(expr.getDefCallArguments().get(0));
      ConcreteExpression arg = process(expr.getDefCallArguments().get(1));
      return isPEval == null || arg == null ? null : isPEval ? factory.peval(arg) : factory.eval(arg);
    } else if (constructor == meta.goalExpr) {
      return factory.goal();
    } else if (constructor == meta.letExpr) {
      Boolean isHave = processBool(expr.getDefCallArguments().get(0));
      Boolean isStrict = processBool(expr.getDefCallArguments().get(1));
      int size = localRefs.size();
      List<ConcreteLetClause> clauses = processArray(expr.getDefCallArguments().get(2), this::processLetClause);
      ConcreteExpression body = process(expr.getDefCallArguments().get(3));
      removeVars(size);
      return isHave == null || isStrict == null || clauses == null || body == null ? null : factory.letExpr(isHave, isStrict, clauses, body);
    } else if (constructor == meta.piExpr) {
      int size = localRefs.size();
      ConcreteParameter parameter = processParameter(expr.getDefCallArguments().get(0));
      ConcreteExpression body = process(expr.getDefCallArguments().get(1));
      removeVars(size);
      return parameter == null || body == null ? null : factory.pi(Collections.singletonList(parameter), body);
    } else if (constructor == meta.typedExpr) {
      ConcreteExpression arg1 = process(expr.getDefCallArguments().get(0));
      ConcreteExpression arg2 = process(expr.getDefCallArguments().get(1));
      return arg1 == null || arg2 == null ? null : factory.typed(arg1, arg2);
    } else if (constructor == meta.localVar) {
      return getLocalRef(expr.getDefCallArguments().get(0));
    } else if (constructor == meta.globalVar) {
      ArendRef ref = getQName(expr.getDefCallArguments().get(0));
      Maybe<List<ConcreteLevel>> pLevels = processMaybe(expr.getDefCallArguments().get(1), e -> processArray(e, this::processLevel));
      Maybe<List<ConcreteLevel>> hLevels = processMaybe(expr.getDefCallArguments().get(2), e -> processArray(e, this::processLevel));
      return ref == null || pLevels == null || hLevels == null ? null : factory.ref(ref, pLevels.just, hLevels.just);
    } else if (constructor == meta.caseExpr) {
      Boolean isSCase = processBool(expr.getDefCallArguments().get(0));
      int size = localRefs.size();
      List<ConcreteCaseArgument> caseArgs = processArray(expr.getDefCallArguments().get(1), e -> {
        List<? extends CoreExpression> fields = processTuple(e, 2);
        if (fields == null) return null;
        CoreExpression orExpr = fields.get(0).normalize(NormalizationMode.WHNF);
        Pair<ConcreteExpression, Boolean> pair = null;
        ConcreteReferenceExpression elimRef = null;
        if (orExpr instanceof CoreConCallExpression conCall) {
          if (conCall.getDefinition() == meta.ext.inl) {
            List<? extends CoreExpression> fields2 = processTuple(conCall.getDefCallArguments().get(0), 2);
            if (fields2 == null) return null;
            ConcreteExpression arg = process(fields2.get(0));
            Boolean asRef = processBool(fields2.get(1));
            pair = arg == null || asRef == null ? null : new Pair<>(arg, asRef);
          } else if (conCall.getDefinition() == meta.ext.inr) {
            elimRef = getLocalRef(conCall.getDefCallArguments().get(0));
            if (elimRef == null) return null;
          }
        }
        if (pair == null && elimRef == null) {
          TypecheckBuildError.report(errorReporter, "Invalid expression. Expected either 'inl' or 'inr'.", orExpr, marker);
          return null;
        }
        Maybe<ConcreteExpression> type = processMaybe(fields.get(1), this::process);
        if (type == null) return null;
        if (pair == null) {
          return factory.caseArg(elimRef, type.just);
        }
        return factory.caseArg(pair.proj1, pair.proj2 ? addRef() : null, type.just);
      });
      Maybe<ConcreteExpression> type = processMaybe(expr.getDefCallArguments().get(2), this::process);
      Maybe<ConcreteExpression> typeLevel = processMaybe(expr.getDefCallArguments().get(3), this::process);
      removeVars(size);
      List<ConcreteClause> clauses = processArray(expr.getDefCallArguments().get(4), e -> {
        List<? extends CoreExpression> fields = processTuple(e, 2);
        if (fields == null) return null;
        int size2 = localRefs.size();
        List<ConcretePattern> patterns = processArray(fields.get(0), this::processPattern);
        Maybe<ConcreteExpression> body = processMaybe(fields.get(1), this::process);
        removeVars(size2);
        return patterns == null || body == null ? null : factory.clause(patterns, body.just);
      });
      return isSCase == null || caseArgs == null || type == null || typeLevel == null || clauses == null ? null : factory.caseExpr(isSCase, caseArgs, type.just, typeLevel.just, clauses);
    } else if (constructor == meta.projExpr) {
      ConcreteExpression arg = process(expr.getDefCallArguments().get(0));
      Integer n = getSmallInteger(expr.getDefCallArguments().get(1));
      return arg == null || n == null ? null : factory.proj(arg, n);
    } else if (constructor == meta.appExpr) {
      ConcreteExpression fun = process(expr.getDefCallArguments().get(0));
      ConcreteExpression arg = process(expr.getDefCallArguments().get(1));
      Boolean isExplicit = processBool(expr.getDefCallArguments().get(2));
      return fun == null || arg == null || isExplicit == null ? null : factory.app(fun, isExplicit, arg);
    } else if (constructor == meta.lamExpr) {
      int size = localRefs.size();
      ConcreteParameter parameter = processParameter(expr.getDefCallArguments().get(0));
      ConcreteExpression body = process(expr.getDefCallArguments().get(1));
      removeVars(size);
      return parameter == null || body == null ? null : factory.lam(Collections.singletonList(parameter), body);
    } else if (constructor == meta.boxExpr) {
      ConcreteExpression arg = process(expr.getDefCallArguments().get(0));
      return arg == null ? null : factory.boxExpr(arg);
    } else if (constructor == meta.numberExpr) {
      BigInteger n = getInteger(expr.getDefCallArguments().get(0));
      return n == null ? null : factory.number(n);
    } else if (constructor == meta.stringExpr) {
      String string = getString(expr.getDefCallArguments().get(0));
      return string == null ? null : factory.string(string);
    } else if (constructor == meta.qNameExpr) {
      ArendRef ref = getQName(expr.getDefCallArguments().get(0));
      return ref == null ? null : factory.qName(ref);
    } else if (constructor == meta.quoteExpr) {
      return factory.core(expr.makeTypedExpression());
    } else {
      TypecheckBuildError.report(errorReporter, expr, marker);
      return null;
    }
  }
}
