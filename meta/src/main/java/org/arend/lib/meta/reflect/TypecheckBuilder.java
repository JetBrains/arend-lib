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
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.util.Pair;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Function;

public class TypecheckBuilder {
  private final TypecheckMeta meta;
  private final ConcreteFactory factory;
  private final ExpressionTypechecker typechecker;
  private final ConcreteExpression marker;
  private final List<ArendRef> localRefs = new ArrayList<>();

  public TypecheckBuilder(TypecheckMeta meta, ConcreteFactory factory, ExpressionTypechecker typechecker, ConcreteExpression marker) {
    this.meta = meta;
    this.factory = factory;
    this.typechecker = typechecker;
    this.marker = marker;
  }

  private int getSmallNatural(CoreExpression expr) {
    BigInteger n = getNatural(expr);
    try {
      return n.intValueExact();
    } catch (ArithmeticException e) {
      throw TypecheckBuildError.makeException("Invalid expression. Expected a small natural number.", expr, marker);
    }
  }

  private int getSmallInteger(CoreExpression expr) {
    BigInteger n = getInteger(expr);
    try {
      return n.intValueExact();
    } catch (ArithmeticException e) {
      throw TypecheckBuildError.makeException("Invalid expression. Expected a small integer.", expr, marker);
    }
  }

  private BigInteger getNatural(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreIntegerExpression) {
      return ((CoreIntegerExpression) expr).getBigInteger();
    } else {
      throw TypecheckBuildError.makeException("Expected a natural number", expr, marker);
    }
  }

  private BigInteger getInteger(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression conCall) {
      boolean isPos = conCall.getDefinition() == meta.ext.prelude.getPos();
      boolean isNeg = conCall.getDefinition() == meta.ext.prelude.getNeg();
      if (isPos || isNeg) {
        BigInteger result = getNatural(conCall.getDefCallArguments().get(0));
        return isNeg ? result.negate() : result;
      }
    }

    throw TypecheckBuildError.makeException("Expected an integer", expr, marker);
  }

  private String getString(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreStringExpression) {
      return ((CoreStringExpression) expr).getString();
    } else {
      throw TypecheckBuildError.makeException("Expected a string", expr, marker);
    }
  }

  private ArendRef getQName(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreQNameExpression) {
      return ((CoreQNameExpression) expr).getRef();
    } else {
      throw TypecheckBuildError.makeException("Expected a QName", expr, marker);
    }
  }

  private ArendRef getVarRef(CoreExpression expr, LevelType levelType) {
    int n = getSmallNatural(expr);
    ArendRef ref = typechecker.getLevelVariable(n, levelType == LevelType.PLEVEL);
    if (ref == null) {
      List<? extends ArendRef> refs = typechecker.getLevelVariables(levelType == LevelType.PLEVEL);
      throw new TypecheckException(new TypecheckingError("Index too large: " + n + ", number of variables: " + refs.size(), marker));
    }
    return ref;
  }

  private ConcreteReferenceExpression getLocalRef(CoreExpression expr) {
    int n = getSmallNatural(expr);
    if (n >= localRefs.size()) {
      int k = n - localRefs.size();
      List<ArendRef> context = typechecker.getFreeReferencesList();
      if (k >= context.size()) {
        throw new TypecheckException(new TypecheckingError("Index too large: " + n + ", number of variables: " + (localRefs.size() + context.size()), marker));
      }
      ArendRef binding = context.get(context.size() - 1 - k);
      ArendRef thisRef = typechecker.getThisReference();
      if (thisRef != null && binding == thisRef) {
        throw new TypecheckException(new TypecheckingError("A reference to \\this binding", marker));
      }
      return factory.ref(binding);
    }
    return factory.ref(localRefs.get(localRefs.size() - 1 - n));
  }

  private ArendRef addRef(String name) {
    if (name.equals("")) return null;
    ArendRef ref = factory.local(name);
    localRefs.add(ref);
    return ref;
  }

  public ConcreteExpression process(CoreExpression expression) {
    expression = expression.normalize(NormalizationMode.WHNF, dataExpr -> dataExpr.getMetaData() instanceof ReflectedExpression);
    if (expression instanceof CoreConCallExpression) {
      return processConCall((CoreConCallExpression) expression);
    } else if (expression instanceof CoreDataExpression) {
      Object data = ((CoreDataExpression) expression).getMetaData();
      if (!(data instanceof ReflectedExpression)) {
        throw new IllegalStateException();
      }
      return ((ReflectedExpression) data).expression;
    } else {
      throw TypecheckBuildError.makeException(expression, marker);
    }
  }

  private <T> List<T> processArray(CoreExpression expr, Function<CoreExpression, T> elementProcessor) {
    List<? extends CoreExpression> elements = expr.getArrayElements();
    if (elements == null) {
      throw TypecheckBuildError.makeException("Invalid expression. Expected an array.", expr, marker);
    }

    List<T> result = new ArrayList<>(elements.size());
    for (CoreExpression element : elements) {
      result.add(elementProcessor.apply(element));
    }
    return result;
  }

  private <T> T processMaybe(CoreExpression expr, Function<CoreExpression, T> elementProcessor) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression conCall) {
      CoreConstructor con = conCall.getDefinition();
      if (con == meta.ext.nothing) {
        return null;
      } else if (con == meta.ext.just) {
        return elementProcessor.apply(conCall.getDefCallArguments().get(0));
      }
    }
    throw TypecheckBuildError.makeException("Invalid expression. Expected a maybe expression.", expr, marker);
  }

  private boolean processBool(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression conCall) {
      if (conCall.getDefinition() == meta.ext.true_) {
        return true;
      } else if (conCall.getDefinition() == meta.ext.false_) {
        return false;
      }
    }

    throw TypecheckBuildError.makeException("Invalid expression. Expected a boolean.", expr, marker);
  }

  private List<? extends CoreExpression> processTuple(CoreExpression expr, int size) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreTupleExpression tuple && tuple.getFields().size() == size) {
      return tuple.getFields();
    } else {
      throw TypecheckBuildError.makeException("Invalid expression. Expected a tuple with " + size + " fields.", expr, marker);
    }
  }

  private ConcreteParameter processParameter(CoreExpression expr) {
    List<? extends CoreExpression> fields = processTuple(expr, 3);
    boolean isExplicit = processBool(fields.get(0));
    String var = getString(fields.get(1));
    ConcreteExpression type = processMaybe(fields.get(2), this::process);
    return type == null ? factory.param(isExplicit, addRef(var)) : var.equals("") ? factory.param(isExplicit, type) : factory.param(isExplicit, Collections.singletonList(addRef(var)), type);
  }

  private void removeVars(int size) {
    localRefs.subList(size, localRefs.size()).clear();
  }

  private ConcreteLetClause processLetClause(CoreExpression expr) {
    List<? extends CoreExpression> fields = processTuple(expr, 4);
    int size = localRefs.size();
    List<ConcreteParameter> parameters = processArray(fields.get(1), this::processParameter);
    ConcreteExpression type = processMaybe(fields.get(2), this::process);
    ConcreteExpression term = process(fields.get(3));
    removeVars(size);
    return factory.letClause(processPattern(fields.get(0)), parameters, type, term);
  }

  private ConcreteLevel processLevel(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression) {
      return processLevelConCall((CoreConCallExpression) expr);
    } else {
      throw TypecheckBuildError.makeException(expr, marker);
    }
  }

  private ConcretePattern processPatternInternal(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreConCallExpression) {
      return processPatternConCall((CoreConCallExpression) expr);
    } else {
      throw TypecheckBuildError.makeException(expr, marker);
    }
  }

  private ConcretePattern processPattern(CoreExpression expr) {
    List<? extends CoreExpression> fields = processTuple(expr, 3);
    ConcretePattern pattern = processPatternInternal(fields.get(0));
    String var = getString(fields.get(1));
    ConcreteExpression type = processMaybe(fields.get(2), this::process);
    ArendRef ref = addRef(var);
    return ref == null ? pattern : pattern.as(ref, type);
  }

  private ConcretePattern processPatternConCall(CoreConCallExpression expr) {
    CoreConstructor constructor = expr.getDefinition();
    if (constructor == meta.tuplePattern) {
      return factory.tuplePattern(processArray(expr.getDefCallArguments().get(0), this::processPattern));
    } else if (constructor == meta.namePattern) {
      ConcreteExpression type = processMaybe(expr.getDefCallArguments().get(1), this::process);
      return factory.refPattern(addRef(getString(expr.getDefCallArguments().get(0))), type);
    } else if (constructor == meta.numberPattern) {
      return factory.numberPattern(getSmallInteger(expr.getDefCallArguments().get(0)));
    } else if (constructor == meta.conPattern) {
      ArendRef ref = getQName(expr.getDefCallArguments().get(0));
      if (ref.isLocalRef()) {
        throw TypecheckBuildError.makeException("Expected a constructor", expr.getDefCallArguments().get(0), marker);
      }
      return factory.conPattern(ref, processArray(expr.getDefCallArguments().get(1), this::processPattern));
    } else {
      throw TypecheckBuildError.makeException(expr, marker);
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

    throw TypecheckBuildError.makeException(expr, marker);
  }

  private ConcreteLevel processLevelConCall(CoreConCallExpression expr) {
    CoreConstructor constructor = expr.getDefinition();
    if (constructor == meta.stdLevel) {
      LevelType type = processLevelType(expr.getDefCallArguments().get(0));
      return type == LevelType.PLEVEL ? factory.lp() : factory.lh();
    } else if (constructor == meta.maxLevel) {
      return factory.maxLevel(processLevel(expr.getDefCallArguments().get(0)), processLevel(expr.getDefCallArguments().get(1)));
    } else if (constructor == meta.sucLevel) {
      return factory.sucLevel(processLevel(expr.getDefCallArguments().get(0)));
    } else if (constructor == meta.numberLevel) {
      return factory.numLevel(getSmallInteger(expr.getDefCallArguments().get(0)));
    } else if (constructor == meta.infLevel) {
      return factory.inf();
    } else if (constructor == meta.varLevel) {
      return factory.varLevel(getVarRef(expr.getDefCallArguments().get(0), processLevelType(expr.getDefCallArguments().get(1))));
    } else {
      throw TypecheckBuildError.makeException(expr, marker);
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
        String var = getString(fields.get(0));
        ConcreteExpression type = process(fields.get(1));
        return factory.param(true, Collections.singletonList(addRef(var)), type);
      });
      removeVars(size);
      return factory.sigma(parameters);
    } else if (constructor == meta.holeExpr) {
      return factory.hole();
    } else if (constructor == meta.universeExpr) {
      return factory.universe(processMaybe(expr.getDefCallArguments().get(0), this::processLevel), processMaybe(expr.getDefCallArguments().get(1), this::processLevel));
    } else if (constructor == meta.tupleExpr) {
      return factory.tuple(processArray(expr.getDefCallArguments().get(0), this::process));
    } else if (constructor == meta.classExtExpr) {
      ConcreteExpression body = process(expr.getDefCallArguments().get(0));
      List<ConcreteClassElement> elements = processArray(expr.getDefCallArguments().get(1), e -> {
        List<? extends CoreExpression> fields = processTuple(e, 2);
        ArendRef ref = getQName(fields.get(0));
        if (ref.isLocalRef()) {
          throw TypecheckBuildError.makeException("Expected a field", fields.get(0), marker);
        }
        return factory.implementation(ref, process(fields.get(1)));
      });
      return factory.classExt(body, elements);
    } else if (constructor == meta.newExpr) {
      return factory.newExpr(process(expr.getDefCallArguments().get(0)));
    } else if (constructor == meta.evalExpr) {
      ConcreteExpression arg = process(expr.getDefCallArguments().get(1));
      return processBool(expr.getDefCallArguments().get(0)) ? factory.peval(arg) : factory.eval(arg);
    } else if (constructor == meta.goalExpr) {
      return factory.goal();
    } else if (constructor == meta.letExpr) {
      int size = localRefs.size();
      List<ConcreteLetClause> clauses = processArray(expr.getDefCallArguments().get(2), this::processLetClause);
      ConcreteExpression body = process(expr.getDefCallArguments().get(3));
      removeVars(size);
      return factory.letExpr(processBool(expr.getDefCallArguments().get(0)), processBool(expr.getDefCallArguments().get(1)), clauses, body);
    } else if (constructor == meta.piExpr) {
      int size = localRefs.size();
      ConcreteParameter parameter = processParameter(expr.getDefCallArguments().get(0));
      ConcreteExpression body = process(expr.getDefCallArguments().get(1));
      removeVars(size);
      return factory.pi(Collections.singletonList(parameter), body);
    } else if (constructor == meta.typedExpr) {
      return factory.typed(process(expr.getDefCallArguments().get(0)), process(expr.getDefCallArguments().get(1)));
    } else if (constructor == meta.localVar) {
      return getLocalRef(expr.getDefCallArguments().get(0));
    } else if (constructor == meta.globalVar) {
      return factory.ref(getQName(expr.getDefCallArguments().get(0)),
        processMaybe(expr.getDefCallArguments().get(1), e -> processArray(e, this::processLevel)),
        processMaybe(expr.getDefCallArguments().get(2), e -> processArray(e, this::processLevel)));
    } else if (constructor == meta.caseExpr) {
      int size = localRefs.size();
      List<ConcreteCaseArgument> caseArgs = processArray(expr.getDefCallArguments().get(1), e -> {
        List<? extends CoreExpression> fields = processTuple(e, 2);
        CoreExpression orExpr = fields.get(0).normalize(NormalizationMode.WHNF);
        Pair<ConcreteExpression, String> pair = null;
        ConcreteReferenceExpression elimRef = null;
        if (orExpr instanceof CoreConCallExpression conCall) {
          if (conCall.getDefinition() == meta.ext.inl) {
            List<? extends CoreExpression> fields2 = processTuple(conCall.getDefCallArguments().get(0), 2);
            ConcreteExpression arg = process(fields2.get(0));
            String asRef = getString(fields2.get(1));
            pair = new Pair<>(arg, asRef);
          } else if (conCall.getDefinition() == meta.ext.inr) {
            CoreExpression arg = conCall.getDefCallArguments().get(0).normalize(NormalizationMode.WHNF);
            boolean ok = true;
            CoreConCallExpression conCall2 = arg instanceof CoreConCallExpression ? (CoreConCallExpression) arg : null;
            if (conCall2 != null && conCall2.getDefinition() == meta.localVar) {
              elimRef = getLocalRef(conCall2.getDefCallArguments().get(0));
            } else if (conCall2 != null && conCall2.getDefinition() == meta.quoteExpr) {
              CoreExpression arg2 = conCall2.getDefCallArguments().get(1).normalize(NormalizationMode.WHNF);
              if (arg2 instanceof CoreReferenceExpression refExpr) {
                var list = typechecker.getFreeVariablesList();
                for (int i = list.size() - 1; i >= 0; i--) {
                  if (list.get(i).proj2 == refExpr.getBinding()) {
                    elimRef = factory.ref(list.get(i).proj1);
                    break;
                  }
                }
                if (elimRef == null) {
                  ok = false;
                }
              } else {
                ok = false;
              }
            } else {
              ok = false;
            }
            if (!ok) {
              throw TypecheckBuildError.makeException("Invalid expression. Expected a local variable.", arg, marker);
            }
          }
        }
        if (pair == null && elimRef == null) {
          throw TypecheckBuildError.makeException("Invalid expression. Expected either 'inl' or 'inr'.", orExpr, marker);
        }
        ConcreteExpression type = processMaybe(fields.get(1), this::process);
        return pair == null ? factory.caseArg(elimRef, type) : factory.caseArg(pair.proj1, addRef(pair.proj2), type);
      });
      ConcreteExpression type = processMaybe(expr.getDefCallArguments().get(2), this::process);
      ConcreteExpression typeLevel = processMaybe(expr.getDefCallArguments().get(3), this::process);
      removeVars(size);
      List<ConcreteClause> clauses = processArray(expr.getDefCallArguments().get(4), e -> {
        List<? extends CoreExpression> fields = processTuple(e, 2);
        int size2 = localRefs.size();
        List<ConcretePattern> patterns = processArray(fields.get(0), this::processPattern);
        ConcreteExpression body = processMaybe(fields.get(1), this::process);
        removeVars(size2);
        return factory.clause(patterns, body);
      });
      return factory.caseExpr(processBool(expr.getDefCallArguments().get(0)), caseArgs, type, typeLevel, clauses);
    } else if (constructor == meta.projExpr) {
      return factory.proj(process(expr.getDefCallArguments().get(0)), getSmallNatural(expr.getDefCallArguments().get(1)));
    } else if (constructor == meta.appExpr) {
      return factory.app(process(expr.getDefCallArguments().get(0)), processBool(expr.getDefCallArguments().get(2)), process(expr.getDefCallArguments().get(1)));
    } else if (constructor == meta.lamExpr) {
      int size = localRefs.size();
      ConcreteParameter parameter = processParameter(expr.getDefCallArguments().get(0));
      ConcreteExpression body = process(expr.getDefCallArguments().get(1));
      removeVars(size);
      return factory.lam(Collections.singletonList(parameter), body);
    } else if (constructor == meta.boxExpr) {
      return factory.boxExpr(process(expr.getDefCallArguments().get(0)));
    } else if (constructor == meta.numberExpr) {
      return factory.number(getNatural(expr.getDefCallArguments().get(0)));
    } else if (constructor == meta.stringExpr) {
      return factory.string(getString(expr.getDefCallArguments().get(0)));
    } else if (constructor == meta.qNameExpr) {
      return factory.qName(getQName(expr.getDefCallArguments().get(0)));
    } else if (constructor == meta.quoteExpr) {
      return factory.core(expr.makeTypedExpression());
    } else {
      throw TypecheckBuildError.makeException(expr, marker);
    }
  }
}
