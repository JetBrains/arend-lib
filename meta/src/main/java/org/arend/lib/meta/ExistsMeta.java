package org.arend.lib.meta;

import org.arend.ext.FreeBindingsModifier;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ArgumentExplicitnessError;
import org.arend.ext.error.TypeMismatchError;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class ExistsMeta implements MetaResolver, MetaDefinition {
  private final StdExtension ext;

  public ExistsMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    if (!new ContextDataChecker().checkContextData(contextData, resolver.getErrorReporter())) {
      return null;
    }
    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());

    List<? extends ConcreteArgument> arguments = contextData.getArguments();
    if (arguments.isEmpty()) {
      return factory.sigma();
    }

    if (arguments.size() == 1) {
      if (!arguments.get(0).isExplicit()) {
        resolver.getErrorReporter().report(new ArgumentExplicitnessError(true, arguments.get(0).getExpression()));
        return null;
      }
      return factory.app(contextData.getReferenceExpression(), true, Collections.singletonList(resolver.resolve(arguments.get(0).getExpression())));
    }

    List<ConcreteParameter> parameters = new ArrayList<>();
    for (ConcreteArgument argument : arguments) {
      if (argument.isExplicit()) {
        ConcreteParameter param = Utils.expressionToParameter(argument.getExpression(), resolver, factory);
        if (param == null) {
          return null;
        }
        parameters.add(param);
      } else {
        List<ArendRef> refs = Utils.getRefs(argument.getExpression(), resolver);
        if (refs == null) {
          return null;
        }
        parameters.add(factory.param(refs, factory.hole()));
      }
    }
    return factory.app(contextData.getReferenceExpression(), true, Collections.singletonList(resolver.resolve(factory.sigma(parameters))));
  }

  private class Processor {
    private final ConcreteFactory factory;
    private final List<ConcreteExpression> arguments = new ArrayList<>();
    private final List<ConcreteParameter> sigmaParams = new ArrayList<>();
    private int arrayIndex = 0;

    private Processor(ConcreteFactory factory) {
      this.factory = factory;
    }

    private ConcreteExpression processParameters(List<? extends ConcreteParameter> parameters, int abstracted, ExpressionTypechecker typechecker) {
      if (parameters.isEmpty()) {
        return getResult();
      }

      ConcreteParameter param = parameters.get(0);
      ConcreteExpression cType = Objects.requireNonNull(param.getType());
      ConcreteExpression aType;
      ConcreteExpression varType;
      TypedExpression typedType;
      CoreExpression type = null;
      if (cType instanceof ConcreteHoleExpression) {
        typedType = typechecker.typecheckType(cType);
        if (typedType == null) return null;
        aType = factory.core(typedType);
      } else {
        CoreExpression[] types = new CoreExpression[] { null };
        Pair<AbstractedExpression, TypedExpression> pair = typechecker.typecheckAbstracted(cType, null, abstracted, typed -> {
          typed = typed.normalizeType();
          types[0] = typed.getType();
          if (!(types[0] instanceof CoreUniverseExpression || types[0] instanceof CorePiExpression || types[0] instanceof CoreClassCallExpression && ((CoreClassCallExpression) types[0]).getDefinition() == ext.prelude.getDArray())) {
            typed = typechecker.coerceToType(typed, cType);
            if (typed == null) {
              typechecker.getErrorReporter().report(new TypeMismatchError(DocFactory.text("\\Type"), types[0], cType));
              return null;
            }
          }
          return typed;
        });
        if (pair == null) return null;
        aType = factory.withData(cType.getData()).abstracted(pair.proj1, new ArrayList<>(arguments));
        typedType = pair.proj2;
        type = types[0];
      }

      List<ArendRef> refs;
      if (type instanceof CorePiExpression) {
        CorePiExpression piType = (CorePiExpression) type;
        CoreParameter piParam = piType.getParameters();
        CoreExpression cod = piType.getCodomain().normalize(NormalizationMode.WHNF);
        if (!(cod instanceof CoreUniverseExpression && !piParam.getNext().hasNext())) {
          typechecker.getErrorReporter().report(new TypeMismatchError(DocFactory.text("_ -> \\Type"), piType, cType));
          return null;
        }
        refs = null;
        varType = factory.withData(cType.getData()).core(piParam.getTypedType());
        List<ArendRef> sigmaRefs = new ArrayList<>(param.getRefList().size());
        for (ArendRef ref : param.getRefList()) {
          sigmaRefs.add(ref != null ? ref : factory.local(ext.renamerFactory.getNameFromType(piParam.getTypeExpr(), null)));
        }
        sigmaParams.add(factory.param(param.isExplicit(), sigmaRefs, varType));
        for (ArendRef ref : sigmaRefs) {
          sigmaParams.add(factory.param(param.isExplicit(), factory.app(factory.withData(cType.getData()).core(typedType), piParam.isExplicit(), factory.ref(ref))));
        }
      } else if (type instanceof CoreClassCallExpression && ((CoreClassCallExpression) type).getDefinition() == ext.prelude.getDArray()) {
        TypedExpression typed = typechecker.typecheck(factory.app(factory.ref(ext.prelude.getFin().getRef()), true, Collections.singletonList(factory.app(factory.ref(ext.prelude.getArrayLength().getRef()), false, Collections.singletonList(aType)))), null);
        if (typed == null) return null;
        varType = factory.core(typed);
        refs = new ArrayList<>(param.getRefList().size());
        for (ArendRef ignored : param.getRefList()) {
          refs.add(factory.local("j" + (arrayIndex == 0 ? "" : arrayIndex)));
          arrayIndex++;
        }
        sigmaParams.add(factory.param(param.isExplicit(), refs, varType));
      } else {
        refs = null;
        varType = factory.withData(cType.getData()).core(typedType);
        sigmaParams.add(factory.param(param.isExplicit(), param.getRefList(), aType));
      }

      if (parameters.size() == 1) {
        return getResult();
      }

      for (ArendRef ref : refs == null ? param.getRefList() : refs) {
        arguments.add(ref == null ? null : factory.ref(ref));
      }

      return typechecker.withFreeBindings(new FreeBindingsModifier().addParams(factory.withData(param.getData()).param(param.isExplicit(), refs == null ? param.getRefList() : refs, varType)), tc -> {
        List<? extends ConcreteParameter> newParams = parameters.subList(1, parameters.size());
        int newAbstracted = abstracted + param.getNumberOfParameters();
        if (refs == null) {
          return processParameters(newParams, newAbstracted, tc);
        }
        List<Pair<ArendRef, CoreBinding>> list = new ArrayList<>(refs.size());
        for (int i = 0; i < refs.size(); i++) {
          TypedExpression result = tc.typecheck(factory.app(factory.ref(ext.prelude.getArrayIndex().getRef()), true, Arrays.asList(factory.withData(cType.getData()).core(typedType), factory.ref(refs.get(i)))), null);
          if (result == null) return null;
          list.add(new Pair<>(param.getRefList().get(i), result.makeEvaluatingBinding(param.getRefList().get(i).getRefName())));
        }
        return tc.withFreeBindings(new FreeBindingsModifier().addRef(list), tc2 -> processParameters(newParams, newAbstracted, tc2));
      });
    }

    private ConcreteExpression getResult() {
      return factory.app(factory.ref(ext.TruncP.getRef()), true, factory.sigma(sigmaParams));
    }
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());
    ConcreteExpression arg = contextData.getArguments().get(0).getExpression();
    ConcreteExpression result = new Processor(factory).processParameters(arg instanceof ConcreteSigmaExpression ? ((ConcreteSigmaExpression) arg).getParameters() : Collections.singletonList(factory.param(true, arg)), 0, typechecker);
    return result == null ? null : typechecker.typecheck(result, contextData.getExpectedType());
  }
}
