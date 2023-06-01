package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteLamExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
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
    ConcreteExpression result;
    if (arg instanceof ConcreteLamExpression lamExpr) {
      ConcreteExpression body = lamExpr.getBody();
      List<? extends ConcreteParameter> lamParams = lamExpr.getParameters();
      ConcreteParameter lamParam0 = lamParams.get(0);
      List<? extends ArendRef> refs = lamParams.get(0).getRefList();
      if (lamParams.size() > 1 || refs.size() > 1) {
        List<ConcreteParameter> params = new ArrayList<>();
        if (refs.size() > 1) {
          ConcreteExpression type = lamParam0.getType();
          if (type == null) {
            for (int i = 1; i < refs.size(); i++) {
              params.add(factory.param(lamParam0.isExplicit(), refs.get(i)));
            }
          } else {
            params.add(factory.param(lamParam0.isExplicit(), refs.subList(1, refs.size()), type));
          }
        }
        params.addAll(lamParams.subList(1, lamParams.size()));
        body = factory.lam(params, body);
      }
      result = body.substitute(Collections.singletonMap(refs.get(0), builder.listToArray(args)));
    } else {
      result = factory.app(arg, true, builder.listToArray(args));
    }
    return typechecker.typecheck(result, contextData.getExpectedType());
  }
}
