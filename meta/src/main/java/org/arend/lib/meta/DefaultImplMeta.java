package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.expr.CoreAbsExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.level.LevelSubstitution;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;
import java.util.List;

public class DefaultImplMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public DefaultImplMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true, true };
  }

  @Override
  public int @Nullable [] desugarArguments(@NotNull List<? extends ConcreteArgument> arguments) {
    if (arguments.size() <= 2) {
      return new int[] {};
    } else {
      int[] result = new int[arguments.size() - 2];
      for (int i = 2; i < arguments.size(); i++) {
        result[i - 2] = i;
      }
      return result;
    }
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    var args = contextData.getArguments();
    ArendRef ref1 = Utils.getReference(args.get(0).getExpression(), typechecker.getErrorReporter());
    if (ref1 == null) return null;
    ArendRef ref2 = Utils.getReference(args.get(1).getExpression(), typechecker.getErrorReporter());
    if (ref2 == null) return null;
    ConcreteExpression arg = args.size() >= 3 ? args.get(2).getExpression() : null;

    CoreDefinition def1 = ext.definitionProvider.getCoreDefinition(ref1);
    if (!(def1 instanceof CoreClassDefinition classDef)) {
      typechecker.getErrorReporter().report(new TypecheckingError("Expected a class", args.get(0).getExpression()));
      return null;
    }
    CoreDefinition def2 = ext.definitionProvider.getCoreDefinition(ref2);
    if (!(def2 instanceof CoreClassField fieldDef)) {
      typechecker.getErrorReporter().report(new TypecheckingError("Expected a field", args.get(1).getExpression()));
      return null;
    }

    CoreAbsExpression expr = classDef.getDefault(fieldDef);
    if (expr == null) {
      typechecker.getErrorReporter().report(new TypecheckingError("The default value is not defined", contextData.getMarker()));
      return null;
    }

    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    if (arg == null) {
      CoreBinding binding = typechecker.getThisBinding();
      arg = binding != null && binding.getTypeExpr() instanceof CoreClassCallExpression classCall && classCall.getDefinition().isSubClassOf(classDef) ? factory.ref(binding) : factory.hole();
    }
    CoreExpression result = typechecker.substitute(expr.getExpression(), LevelSubstitution.EMPTY, Collections.singletonList(new SubstitutionPair(expr.getBinding(), arg)));
    return result == null ? null : args.size() <= 3 ? result.computeTyped() : typechecker.typecheck(factory.app(factory.core(result.computeTyped()), args.subList(3, args.size())), contextData.getExpectedType());
  }
}
