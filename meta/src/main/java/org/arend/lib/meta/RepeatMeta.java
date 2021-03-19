package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.util.MetaInvocationMeta;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;
import java.util.List;

public class RepeatMeta extends MetaInvocationMeta {
  private final StdExtension ext;

  public RepeatMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { false, true, true };
  }

  @Override
  protected boolean keepMetaArgument() {
    return true;
  }

  @Override
  protected boolean allowNonMeta() {
    return false;
  }

  private ConcreteExpression computeConcrete(int steps, List<? extends ConcreteArgument> args, ConcreteFactory factory) {
    ConcreteExpression result = args.get(1).getExpression();
    for (int i = 0; i < steps; i++) {
      result = factory.app(args.get(0).getExpression(), true, Collections.singletonList(result));
    }
    return factory.app(result, args.subList(2, args.size()));
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(MetaDefinition meta, List<ConcreteExpression> implicitArguments, @NotNull List<? extends ConcreteArgument> arguments) {
    int steps = -1;
    if (!implicitArguments.isEmpty()) {
      steps = Utils.getNumber(implicitArguments.get(0), null);
      if (steps < 0) {
        return null;
      }
    }

    if (steps == -1) {
      return ext.factory.app(ext.factory.app(arguments.get(0).getExpression(), true, Collections.singletonList(ext.factory.hole())), arguments.subList(2, arguments.size()));
    } else {
      return computeConcrete(steps, arguments, ext.factory);
    }
  }

  @Override
  public TypedExpression invokeMeta(MetaDefinition meta, List<ConcreteExpression> implicitArguments, ExpressionTypechecker typechecker, ContextData contextData) {
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    List<? extends ConcreteArgument> args = contextData.getArguments();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());

    int steps = -1;
    if (!implicitArguments.isEmpty()) {
      steps = Utils.getNumber(implicitArguments.get(0), errorReporter);
      if (steps < 0) {
        return null;
      }
    }

    if (steps == -1) {
      typechecker.checkCancelled();

      TypedExpression result = Utils.tryTypecheck(typechecker, tc -> tc.typecheck(factory.app(args.get(0).getExpression(), true, Collections.singletonList(factory.app(refExpr, args.subList(0, 2)))), args.size() <= 2 ? contextData.getExpectedType() : null));
      if (result == null) {
        return typechecker.typecheck(factory.app(args.get(1).getExpression(), args.subList(2, args.size())), contextData.getExpectedType());
      }
      if (args.size() <= 2) {
        return result;
      }
      return typechecker.typecheck(factory.app(factory.core("repeat _", result), args.subList(2, args.size())), contextData.getExpectedType());
    } else {
      return typechecker.typecheck(computeConcrete(steps, args, factory), contextData.getExpectedType());
    }
  }
}
