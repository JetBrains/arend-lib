package org.arend.lib.util;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.*;
import org.arend.ext.instance.InstanceSearchParameters;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.reference.MetaRef;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Function;

public class Utils {
  public static int getNumber(ConcreteExpression expression, ErrorReporter errorReporter) {
    if (expression instanceof ConcreteNumberExpression) {
      return ((ConcreteNumberExpression) expression).getNumber().intValue();
    } else {
      if (errorReporter != null) {
        errorReporter.report(new TypecheckingError("Expected a number", expression));
      }
      return -1;
    }
  }

  public static List<? extends ConcreteExpression> getArgumentList(ConcreteExpression expr) {
    return expr instanceof ConcreteTupleExpression ? ((ConcreteTupleExpression) expr).getFields() : Collections.singletonList(expr);
  }

  public static CoreFunCallExpression toEquality(CoreExpression expression, ErrorReporter errorReporter, ConcreteSourceNode sourceNode) {
    CoreFunCallExpression equality = expression.toEquality();
    if (equality == null && errorReporter != null && !expression.reportIfError(errorReporter, sourceNode)) {
      errorReporter.report(new TypeMismatchError(DocFactory.text("_ = _"), expression, sourceNode));
    }
    return equality;
  }

  public static CoreExpression getAppArguments(CoreExpression expression, int numberOfArgs, List<CoreExpression> args) {
    CoreExpression result = getAppArgumentsRev(expression, numberOfArgs, args);
    Collections.reverse(args);
    return result;
  }

  private static CoreExpression getAppArgumentsRev(CoreExpression expression, int numberOfArgs, List<CoreExpression> args) {
    if (numberOfArgs <= 0) {
      return expression;
    }
    expression = expression.normalize(NormalizationMode.WHNF).getUnderlyingExpression();
    if (expression instanceof CoreAppExpression) {
      args.add(((CoreAppExpression) expression).getArgument());
      return getAppArgumentsRev(((CoreAppExpression) expression).getFunction(), numberOfArgs - 1, args);
    }
    return expression;
  }

  public static int numberOfExplicitParameters(CoreDefinition def) {
    int result = def instanceof CoreFunctionDefinition ? numberOfExplicitPiParameters(((CoreFunctionDefinition) def).getResultType())
      : def instanceof CoreClassField ? numberOfExplicitPiParameters(((CoreClassField) def).getResultType()) : 0;
    for (CoreParameter parameter = def.getParameters(); parameter.hasNext(); parameter = parameter.getNext()) {
      if (parameter.isExplicit()) {
        result++;
      }
    }
    return result;
  }

  public static int numberOfExplicitPiParameters(CoreExpression type) {
    List<CoreParameter> parameters = new ArrayList<>();
    type.getPiParameters(parameters);

    int result = 0;
    for (CoreParameter parameter : parameters) {
      if (parameter.isExplicit()) {
        result++;
      }
    }
    return result;
  }

  public static int parametersSize(CoreParameter param) {
    int s = 0;
    for (; param.hasNext(); param = param.getNext()) {
      s++;
    }
    return s;
  }

  public static ConcreteExpression addArguments(ConcreteExpression expr, ConcreteFactory factory, int numberOfArgs, boolean addGoals) {
    if (numberOfArgs <= 0) {
      return expr;
    }

    List<ConcreteExpression> args = new ArrayList<>(numberOfArgs);
    for (int i = 0; i < numberOfArgs; i++) {
      args.add(addGoals ? factory.goal() : factory.hole());
    }
    return factory.app(expr, true, args);
  }

  public static List<ConcreteExpression> addArguments(ConcreteExpression expr, StdExtension ext, int expectedParameters, boolean addGoals) {
    ConcreteReferenceExpression refExpr = null;
    if (expr instanceof ConcreteReferenceExpression) {
      refExpr = (ConcreteReferenceExpression) expr;
    } else if (expr instanceof ConcreteAppExpression) {
      ConcreteExpression fun = ((ConcreteAppExpression) expr).getFunction();
      if (fun instanceof ConcreteReferenceExpression) {
        refExpr = (ConcreteReferenceExpression) fun;
      }
    }

    if (refExpr == null) {
      return Collections.emptyList();
    }

    int numberOfArgs = 0;
    ArendRef ref = refExpr.getReferent();
    if (ref instanceof MetaRef) {
      MetaDefinition meta = ((MetaRef) ref).getDefinition();
      if (meta instanceof BaseMetaDefinition) {
        boolean[] explicitness = ((BaseMetaDefinition) meta).argumentExplicitness();
        if (explicitness != null) {
          for (boolean explicit : explicitness) {
            if (explicit) {
              numberOfArgs++;
            }
          }
        }
      }
    } else {
      CoreDefinition argDef = ext.definitionProvider.getCoreDefinition(ref);
      if (argDef == null) {
        return Collections.emptyList();
      }
      numberOfArgs = numberOfExplicitParameters(argDef) - expectedParameters;
    }

    if (expr instanceof ConcreteAppExpression && numberOfArgs > 0) {
      for (ConcreteArgument argument : ((ConcreteAppExpression) expr).getArguments()) {
        if (argument.isExplicit()) {
          numberOfArgs--;
        }
      }
    }

    if (numberOfArgs <= 0) {
      return Collections.emptyList();
    }

    ConcreteFactory factory = ext.factory.withData(expr.getData());
    List<ConcreteExpression> args = new ArrayList<>(numberOfArgs);
    for (int i = 0; i < numberOfArgs; i++) {
      args.add(addGoals ? factory.goal() : factory.hole());
    }
    return args;
  }

  public static TypedExpression typecheckWithAdditionalArguments(ConcreteExpression expr, ExpressionTypechecker typechecker, StdExtension ext, int expectedParameters, boolean addGoals) {
    List<ConcreteExpression> args = addArguments(expr, ext, expectedParameters, addGoals);
    TypedExpression result = typechecker.typecheck(args.isEmpty() ? expr : ext.factory.withData(expr.getData()).app(expr, true, args), null);
    if (result == null) {
      return null;
    }

    List<CoreParameter> parameters = new ArrayList<>();
    result.getType().getPiParameters(parameters);
    if (parameters.isEmpty()) {
      return result;
    }

    ConcreteFactory factory = ext.factory.withData(expr.getData());
    List<ConcreteArgument> arguments = new ArrayList<>();
    for (CoreParameter parameter : parameters) {
      if (parameter.isExplicit()) {
        if (expectedParameters <= 0) {
          arguments.add(factory.arg(addGoals ? factory.goal() : factory.hole(), true));
        } else {
          expectedParameters--;
        }
      } else {
        arguments.add(factory.arg(factory.hole(), false));
      }
    }
    if (arguments.isEmpty()) {
      return result;
    }

    return typechecker.typecheck(factory.app(factory.core("_", result), arguments), null);
  }

  private static class MyException extends RuntimeException {}

  public static <T> T tryWithSavedState(ExpressionTypechecker tc, Function<ExpressionTypechecker, T> action) {
    boolean allowed = tc.deferredMetasAllowed();
    try {
      tc.allowDeferredMetas(false);
      ErrorReporter errorReporter = tc.getErrorReporter();
      return tc.withErrorReporter(error -> {
        if (error.level == GeneralError.Level.ERROR) {
          throw new MyException();
        }
        errorReporter.report(error);
      }, action);
    } catch (MyException e) {
      tc.loadSavedState();
      return null;
    } finally {
      tc.allowDeferredMetas(allowed);
    }
  }

  public static <T> T tryTypecheck(ExpressionTypechecker typechecker, Function<ExpressionTypechecker, T> action) {
    return typechecker.withCurrentState(tc -> tryWithSavedState(tc, action));
  }

  public static TypedExpression findInstance(InstanceSearchParameters parameters, CoreClassField classifyingField, CoreExpression classifyingExpr, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
    if (classifyingExpr instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) classifyingExpr).getDefinition() == classifyingField) {
      TypedExpression result = ((CoreFieldCallExpression) classifyingExpr).getArgument().computeTyped();
      CoreExpression type = result.getType().normalize(NormalizationMode.WHNF);
      return type instanceof CoreClassCallExpression && parameters.testClass(((CoreClassCallExpression) type).getDefinition()) ? result : null;
    } else {
      return typechecker.findInstance(parameters, classifyingExpr, null, marker);
    }
  }

  public static CoreClassCallExpression getClassCall(CoreExpression type) {
    CoreExpression instanceType = type.normalize(NormalizationMode.WHNF);
    return instanceType instanceof CoreClassCallExpression ? (CoreClassCallExpression) instanceType : null;
  }

  public static Pair<TypedExpression, CoreClassCallExpression> findInstanceWithClassCall(InstanceSearchParameters parameters, CoreClassField classifyingField, CoreExpression classifyingExpr, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
    if (classifyingExpr instanceof CoreFieldCallExpression) {
      if (((CoreFieldCallExpression) classifyingExpr).getDefinition() == classifyingField) {
        TypedExpression instance = ((CoreFieldCallExpression) classifyingExpr).getArgument().computeTyped();
        CoreClassCallExpression classCall = getClassCall(instance.getType());
        if (classCall != null && parameters.testClass(classCall.getDefinition())) {
          return new Pair<>(instance, classCall);
        }
      }
      return null;
    }

    TypedExpression instance = typechecker.findInstance(parameters, classifyingExpr, null, marker);
    if (instance != null) {
      CoreClassCallExpression classCall = getClassCall(instance.getType());
      if (classCall != null) {
        return new Pair<>(instance, classCall);
      }
    }

    return null;
  }

  public static Pair<TypedExpression, CoreClassCallExpression> findInstanceWithClassCall(InstanceSearchParameters parameters, CoreClassField classifyingField, CoreExpression classifyingExpr, ExpressionTypechecker typechecker, ConcreteSourceNode marker, CoreClassDefinition forcedClass) {
    return typechecker.withCurrentState(tc -> {
      Pair<TypedExpression, CoreClassCallExpression> result = findInstanceWithClassCall(parameters, classifyingField, classifyingExpr, typechecker, marker);
      if (result == null) {
        if (forcedClass != null) {
          typechecker.getErrorReporter().report(new InstanceInferenceError(typechecker.getExpressionPrettifier(), forcedClass.getRef(), classifyingExpr, marker));
        } else {
          tc.loadSavedState();
        }
        return null;
      }

      CoreExpression classifyingImpl = result.proj2.getImplementation(classifyingField, result.proj1);
      if (classifyingImpl != null && !Boolean.TRUE.equals(tryWithSavedState(tc, tc2 -> tc2.compare(classifyingImpl, classifyingExpr, CMP.LE, marker, true, true, false)))) {
        if (forcedClass != null) {
          typechecker.getErrorReporter().report(new InstanceInferenceError(typechecker.getExpressionPrettifier(), forcedClass.getRef(), classifyingExpr, marker, new CoreExpression[]{result.proj1.getExpression()}));
        } else {
          tc.loadSavedState();
        }
        return null;
      }
      CoreExpression expr = result.proj1.getExpression();
      if (expr instanceof CoreFunCallExpression funCall) {
        for (CoreExpression argument : funCall.getDefCallArguments()) {
          if (argument instanceof CoreInferenceReferenceExpression infExpr && infExpr.getSubstExpression() == null) {
            tc.loadSavedState();
            return null;
          }
        }
      }
      return result;
    });
  }

  public static boolean safeCompare(ExpressionTypechecker typechecker, UncheckedExpression expr1, UncheckedExpression expr2, CMP cmp, ConcreteSourceNode marker, boolean allowEquations, boolean normalize, boolean useTypes) {
    return expr1.getUnderlyingExpression() == expr2.getUnderlyingExpression() || typechecker.withCurrentState(tc -> {
      if (tc.compare(expr1, expr2, cmp, marker, allowEquations, normalize, useTypes)) {
        return true;
      }
      tc.loadSavedState();
      return false;
    });
  }

  public static boolean isProp(CoreExpression type) {
    CoreExpression typeType = type.normalize(NormalizationMode.WHNF).computeType().normalize(NormalizationMode.WHNF);
    return typeType instanceof CoreUniverseExpression && ((CoreUniverseExpression) typeType).getSort().isProp();
  }

  public static CoreExpression minimizeToProp(CoreExpression type) {
    type = type.normalize(NormalizationMode.WHNF).minimizeLevels();
    CoreExpression typeType = type.computeType().normalize(NormalizationMode.WHNF);
    return typeType instanceof CoreUniverseExpression && ((CoreUniverseExpression) typeType).getSort().isProp() ? type : null;
  }

  public static List<CoreClassField> getNotImplementedField(CoreClassCallExpression classCall) {
    List<CoreClassField> classFields = new ArrayList<>();
    for (CoreClassField field : classCall.getDefinition().getNotImplementedFields()) {
      if (!classCall.isImplementedHere(field)) {
        classFields.add(field);
      }
    }
    return classFields;
  }

  public static CoreExpression unfoldType(CoreExpression type) {
    while (type instanceof CoreFunCallExpression && ((CoreFunCallExpression) type).getDefinition().getKind() == CoreFunctionDefinition.Kind.TYPE) {
      CoreExpression result = ((CoreFunCallExpression) type).evaluate();
      if (result == null) break;
      type = result.normalize(NormalizationMode.WHNF);
    }
    return type;
  }

  public static Boolean isArrayEmpty(CoreExpression type, StdExtension ext) {
    type = type.normalize(NormalizationMode.WHNF);
    if (!(type instanceof CoreClassCallExpression && ((CoreClassCallExpression) type).getDefinition() == ext.prelude.getDArray())) return null;
    CoreExpression length = ((CoreClassCallExpression) type).getAbsImplementationHere(ext.prelude.getArrayLength());
    if (length == null) return null;
    length = length.normalize(NormalizationMode.WHNF);
    return length instanceof CoreIntegerExpression ? (Boolean) ((CoreIntegerExpression) length).getBigInteger().equals(BigInteger.ZERO) : length instanceof CoreConCallExpression && ((CoreConCallExpression) length).getDefinition() == ext.prelude.getSuc() ? false : null;
  }

  private static boolean getRef(ConcreteExpression expr, ExpressionResolver resolver, List<ArendRef> refs) {
    if (expr instanceof ConcreteReferenceExpression) {
      ArendRef ref = ((ConcreteReferenceExpression) expr).getReferent();
      if (resolver.isLongUnresolvedReference(ref)) {
        return false;
      }
      refs.add(ref);
      return true;
    }

    if (expr instanceof ConcreteHoleExpression) {
      refs.add(null);
      return true;
    }

    return false;
  }

  public static List<ArendRef> getRefs(ConcreteExpression expr, ExpressionResolver resolver) {
    List<ArendRef> result = new ArrayList<>();
    for (ConcreteArgument argument : expr.getArgumentsSequence()) {
      if (!argument.isExplicit() || !getRef(argument.getExpression(), resolver, result)) {
        resolver.getErrorReporter().report(new NameResolverError("Cannot parse references", expr));
        return null;
      }
    }
    return result;
  }

  private static boolean getTupleOfRefs(ConcreteExpression expr, ExpressionResolver resolver, List<ArendRef> refs) {
    if (expr instanceof ConcreteReferenceExpression) {
      ArendRef ref = ((ConcreteReferenceExpression) expr).getReferent();
      if (resolver.isLongUnresolvedReference(ref)) {
        return false;
      }
      refs.add(ref);
      return true;
    }

    if (expr instanceof ConcreteHoleExpression) {
      refs.add(null);
      return true;
    }

    if (expr instanceof ConcreteTupleExpression) {
      for (ConcreteExpression field : ((ConcreteTupleExpression) expr).getFields()) {
        if (field instanceof ConcreteReferenceExpression) {
          ArendRef ref = ((ConcreteReferenceExpression) field).getReferent();
          if (resolver.isLongUnresolvedReference(ref)) {
            return false;
          }
          refs.add(ref);
        } else if (field instanceof ConcreteHoleExpression) {
          refs.add(null);
        } else {
          return false;
        }
      }
      return true;
    }

    return false;
  }

  public static List<ArendRef> getTuplesOfRefs(ConcreteExpression expr, ExpressionResolver resolver) {
    List<ArendRef> result = new ArrayList<>();
    for (ConcreteArgument argument : expr.getArgumentsSequence()) {
      if (!argument.isExplicit() || !getTupleOfRefs(argument.getExpression(), resolver, result)) {
        resolver.getErrorReporter().report(new NameResolverError("Cannot parse references", expr));
        return null;
      }
    }
    return result;
  }

  public static ConcreteParameter expressionToParameter(ConcreteExpression expr, ExpressionResolver resolver, ConcreteFactory factory) {
    if (expr instanceof ConcreteTypedExpression typedExpr) {
      List<ArendRef> refs = getTuplesOfRefs(typedExpr.getExpression(), resolver);
      if (refs == null) {
        return null;
      }
      return factory.param(refs, typedExpr.getType());
    } else {
      return factory.param(Collections.emptyList(), expr);
    }
  }

  public static ConcreteExpression normalResolve(ExpressionResolver resolver, ContextData contextData, ConcreteExpression leftArg, ConcreteExpression rightArg, ConcreteFactory factory) {
    factory = factory.withData(contextData.getMarker());
    List<ConcreteArgument> args = new ArrayList<>(contextData.getArguments().size());
    for (ConcreteArgument argument : contextData.getArguments()) {
      args.add(factory.arg(resolver.resolve(argument.getExpression()), argument.isExplicit()));
    }
    ConcreteExpression result = factory.app(contextData.getReferenceExpression(), args);
    if (leftArg != null) {
      result = factory.app(result, true, resolver.resolve(leftArg));
    }
    if (rightArg != null) {
      rightArg = resolver.resolve(rightArg);
      if (leftArg == null) {
        ArendRef ref = factory.local("p0");
        result = factory.lam(Collections.singletonList(factory.param(ref)), factory.app(result, true, factory.ref(ref), rightArg));
      } else {
        result = factory.app(result, true, rightArg);
      }
    }
    return result;
  }

  public static ConcreteExpression resolvePrefixAsInfix(MetaResolver metaResolver, ExpressionResolver resolver, ContextData contextData, ConcreteFactory factory) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    int implicitArgs = 0;
    for (ConcreteArgument arg : args) {
      if (!arg.isExplicit()) {
        implicitArgs++;
      }
    }
    if (args.size() <= implicitArgs + 2 && (args.size() <= implicitArgs || args.get(implicitArgs).isExplicit()) && (args.size() <= implicitArgs + 1 || args.get(implicitArgs + 1).isExplicit())) {
      contextData.setArguments(args.subList(0, implicitArgs));
      return metaResolver.resolveInfix(resolver, contextData, args.size() > implicitArgs ? args.get(implicitArgs).getExpression() : null, args.size() > implicitArgs + 1 ? args.get(implicitArgs + 1).getExpression() : null);
    } else {
      return normalResolve(resolver, contextData, null, null, factory);
    }
  }

  public static ArendRef getReference(ConcreteExpression expr, ErrorReporter errorReporter) {
    if (expr instanceof ConcreteReferenceExpression refExpr) {
      return refExpr.getReferent();
    }

    errorReporter.report(new TypecheckingError("Expected a reference", expr));
    return null;
  }

  public static CoreExpression getClassifyingExpression(CoreClassCallExpression classCall, TypedExpression thisExpr) {
    CoreClassField field = classCall.getDefinition().getClassifyingField();
    return field == null ? null : classCall.getImplementation(field, thisExpr);
  }
}
