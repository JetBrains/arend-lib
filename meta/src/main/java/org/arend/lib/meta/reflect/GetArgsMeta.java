package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class GetArgsMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public GetArgsMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  private ConcreteExpression argsToArray(List<ConcreteExpression> args, ReflectBuilder builder, ConcreteFactory factory) {
    return args.isEmpty() ? factory.app(factory.ref(ext.prelude.getEmptyArray().getRef()), false, factory.lam(Collections.singletonList(factory.param(null)), factory.sigma(factory.param(true, factory.ref(ext.tcMeta.ConcreteExpr.getRef())), factory.param(true, factory.ref(ext.false_.getDataType().getRef()))))) : builder.listToArray(args);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    List<? extends ConcreteArgument> arguments = contextData.getArguments();
    List<ConcreteExpression> args = new ArrayList<>();
    ReflectBuilder builder = new ReflectBuilder(typechecker, ext, factory);
    for (int i = 1; i < arguments.size(); i++) {
      ConcreteArgument arg = arguments.get(i);
      args.add(factory.tuple(factory.app(factory.ref(ext.reflectRef), true, arg.getExpression()), builder.makeBool(arg.isExplicit())));
    }
    ConcreteExpression arg = arguments.get(0).getExpression();
    return typechecker.typecheck(Utils.applyExpression(arg, argsToArray(args, builder, factory), factory), contextData.getExpectedType());
  }
}
