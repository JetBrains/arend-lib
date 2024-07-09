package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.instance.InstanceSearchParameters;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.ext.util.Wrapper;
import org.arend.lib.StdExtension;
import org.arend.lib.error.SimplifyError;
import org.arend.lib.error.TypeError;
import org.arend.lib.meta.RewriteMeta;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

public class SimplifyMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public SimplifyMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }



  @Override
  public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    var refExpr = contextData.getReferenceExpression();
    boolean isForward = contextData.getExpectedType() == null;
    CoreExpression expectedType = contextData.getExpectedType();
    List<? extends ConcreteArgument> args = contextData.getArguments();

    if (isForward && args.isEmpty()) {
      return null;
    }

    var factory = ext.factory.withData(refExpr.getData());
    var expression = args.isEmpty() ? factory.ref(ext.prelude.getIdp().getRef()) : args.get(0).getExpression();
    CoreExpression type;

    if (isForward) {
      var checkedExpr = typechecker.typecheck(expression, null);
      type = checkedExpr == null ? null : checkedExpr.getType();
    } else {
      type = expectedType == null ? null : expectedType.getUnderlyingExpression();
    }

    if (type == null) {
      return Utils.typecheckWithAdditionalArguments(expression, typechecker, ext, 0, false);
    }

    var transportedExpr = new Simplifier(ext, typechecker, refExpr, factory, typechecker.getErrorReporter()).simplifyTypeOfExpression(expression, type, isForward);
    return transportedExpr == null ? null : typechecker.typecheck(transportedExpr, expectedType);
  }
}
