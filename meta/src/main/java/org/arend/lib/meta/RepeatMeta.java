package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.GeneralError;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;
import java.util.List;

public class RepeatMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public RepeatMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  protected @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false, true, true };
  }

  private ConcreteExpression computeConcrete(int steps, List<? extends ConcreteArgument> args, int currentArg, ConcreteFactory factory) {
    ConcreteExpression result = args.get(currentArg + 1).getExpression();
    for (int i = 0; i < steps; i++) {
      result = factory.app(args.get(currentArg).getExpression(), true, Collections.singletonList(result));
    }
    return factory.app(result, args.subList(currentArg + 2, args.size()));
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    int steps = -1;
    int currentArg = 0;
    if (!arguments.get(0).isExplicit()) {
      steps = Utils.getNumber(arguments.get(0).getExpression(), null);
      if (steps < 0) {
        return null;
      }
      currentArg++;
    }

    if (steps == -1) {
      return ext.factory.app(ext.factory.app(arguments.get(currentArg).getExpression(), true, Collections.singletonList(ext.factory.hole())), arguments.subList(currentArg + 2, arguments.size()));
    } else {
      return computeConcrete(steps, arguments, currentArg, ext.factory);
    }
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    List<? extends ConcreteArgument> args = contextData.getArguments();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());

    int steps = -1;
    int currentArg = 0;
    if (!args.get(0).isExplicit()) {
      steps = Utils.getNumber(args.get(0).getExpression(), errorReporter);
      if (steps < 0) {
        return null;
      }
      currentArg++;
    }

    if (steps == -1) {
      typechecker.checkCancelled();

      TypedExpression result;
      try {
        int finalCurrentArg = currentArg;
        result = typechecker.withErrorReporter(error -> {
          if (error.level == GeneralError.Level.ERROR || error.level == GeneralError.Level.GOAL) {
            throw new MyException();
          }
        }, tc -> tc.typecheck(factory.app(args.get(finalCurrentArg).getExpression(), true, Collections.singletonList(factory.app(refExpr, args.subList(finalCurrentArg, finalCurrentArg + 2)))), args.size() <= finalCurrentArg + 2 ? contextData.getExpectedType() : null));
      } catch (MyException e) {
        result = null;
      }
      if (result == null) {
        return typechecker.typecheck(factory.app(args.get(currentArg + 1).getExpression(), args.subList(currentArg + 2, args.size())), contextData.getExpectedType());
      }
      if (args.size() <= currentArg + 2) {
        return result;
      }
      return typechecker.typecheck(factory.app(factory.core("repeat _", result), args.subList(currentArg + 2, args.size())), contextData.getExpectedType());
    } else {
      return typechecker.typecheck(computeConcrete(steps, args, currentArg, factory), contextData.getExpectedType());
    }
  }

  private static class MyException extends RuntimeException {}
}
