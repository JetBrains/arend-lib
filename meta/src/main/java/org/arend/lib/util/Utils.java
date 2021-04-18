package org.arend.lib.util;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.TypeMismatchError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.instance.InstanceSearchParameters;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.MetaRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.TypedExpression;
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
    if (equality == null && errorReporter != null && !expression.isError()) {
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

  public static <T> T tryTypecheck(ExpressionTypechecker typechecker, Function<ExpressionTypechecker, T> action) {
    return typechecker.withCurrentState(tc -> {
      try {
        return tc.withErrorReporter(error -> {
          if (error.level == GeneralError.Level.ERROR) {
            throw new MyException();
          }
        }, action);
      } catch (MyException e) {
        tc.loadSavedState();
        return null;
      }
    });
  }

  public static TypedExpression findInstance(InstanceSearchParameters parameters, CoreClassField classifyingField, CoreExpression classifyingExpr, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
    CoreExpression expr = classifyingExpr.normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) expr).getDefinition() == classifyingField) {
      TypedExpression result = ((CoreFieldCallExpression) expr).getArgument().computeTyped();
      CoreExpression type = result.getType().normalize(NormalizationMode.WHNF);
      return type instanceof CoreClassCallExpression && parameters.testClass(((CoreClassCallExpression) type).getDefinition()) ? result : null;
    } else {
      return typechecker.findInstance(parameters, expr, null, marker);
    }
  }

  public static boolean safeCompare(ExpressionTypechecker typechecker, UncheckedExpression expr1, UncheckedExpression expr2, CMP cmp, ConcreteSourceNode marker, boolean allowEquations, boolean normalize) {
    return typechecker.withCurrentState(tc -> {
      if (tc.compare(expr1, expr2, cmp, marker, allowEquations, normalize)) {
        return true;
      }
      tc.loadSavedState();
      return false;
    });
  }

  public static boolean isProp(CoreExpression type) {
    CoreExpression typeType = type.computeType().normalize(NormalizationMode.WHNF);
    return typeType instanceof CoreUniverseExpression && ((CoreUniverseExpression) typeType).getSort().isProp();
  }

  public static List<CoreClassField> getNotImplementedField(CoreClassCallExpression classCall) {
    List<CoreClassField> classFields = new ArrayList<>();
    for (CoreClassField field : classCall.getDefinition().getFields()) {
      if (!classCall.isImplemented(field)) {
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
    if (!(type instanceof CoreClassCallExpression && ((CoreClassCallExpression) type).getDefinition() == ext.prelude.getArray())) return null;
    CoreExpression length = ((CoreClassCallExpression) type).getAbsImplementationHere(ext.prelude.getArrayLength());
    if (length == null) return null;
    length = length.normalize(NormalizationMode.WHNF);
    return length instanceof CoreIntegerExpression ? (Boolean) ((CoreIntegerExpression) length).getBigInteger().equals(BigInteger.ZERO) : length instanceof CoreConCallExpression && ((CoreConCallExpression) length).getDefinition() == ext.prelude.getSuc() ? false : null;
  }
}
