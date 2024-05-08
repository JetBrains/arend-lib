package org.arend.lib.meta;

import org.arend.ext.FreeBindingsModifier;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.*;
import org.arend.ext.error.ArgumentExplicitnessError;
import org.arend.ext.error.TypeMismatchError;
import org.arend.ext.error.TypecheckingError;
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
  private final Kind kind;

  public ExistsMeta(StdExtension ext, Kind kind) {
    this.ext = ext;
    this.kind = kind;
  }

  public enum Kind { TRUNCATED, SIGMA, PI }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    if (!new ContextDataChecker().checkContextData(contextData, resolver.getErrorReporter())) {
      return null;
    }
    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());

    List<? extends ConcreteArgument> arguments = contextData.getArguments();
    for (int i = 0; i < arguments.size(); i++) {
      if (arguments.get(i).isExplicit() && arguments.get(i).getExpression() instanceof ConcreteReferenceExpression refExpr && !resolver.isLongUnresolvedReference(refExpr.getReferent())) {
        ArendRef ref = refExpr.getReferent();
        ref = resolver.isUnresolved(ref) ? resolver.resolveName(ref.getRefName()) : resolver.getOriginalRef(ref);
        if (ref != null && (ref == ext.existsMetaRef || ref == ext.forallMetaRef || ref == ext.givenMetaRef)) {
          List<ConcreteArgument> newArgs = new ArrayList<>(i + 1);
          newArgs.addAll(arguments.subList(0, i));
          newArgs.add(factory.arg(factory.app(arguments.get(i).getExpression(), arguments.subList(i + 1, arguments.size())), true));
          arguments = newArgs;
          break;
        }
      }
    }

    if (arguments.isEmpty()) {
      if (kind == Kind.PI) {
        resolver.getErrorReporter().report(new ArgumentExplicitnessError(true, contextData.getMarker()));
        return null;
      }
      return factory.sigma();
    }

    if (arguments.size() == 1) {
      if (!arguments.get(0).isExplicit()) {
        resolver.getErrorReporter().report(new ArgumentExplicitnessError(true, arguments.get(0).getExpression()));
        return null;
      }
      return factory.app(contextData.getReferenceExpression(), true, Collections.singletonList(resolver.resolve(arguments.get(0).getExpression())));
    }

    ConcreteExpression codomain = null;
    List<ConcreteParameter> parameters = new ArrayList<>();
    for (int i = 0; i < arguments.size(); i++) {
      ConcreteArgument argument = arguments.get(i);
      ConcreteFactory argFactory = factory.withData(argument.getExpression().getData());
      if (kind == Kind.PI) {
        if (i == arguments.size() - 1) {
          if (!argument.isExplicit()) {
            resolver.getErrorReporter().report(new ArgumentExplicitnessError(true, argument.getExpression()));
            return null;
          }
          if (argument.getExpression() instanceof ConcreteTypedExpression) {
            resolver.getErrorReporter().report(new TypecheckingError("Expected a type without variables", contextData.getMarker()));
            return null;
          }
        }
        if (argument.getExpression() instanceof ConcreteTypedExpression || argument.isExplicit()) {
          if (i == arguments.size() - 1) {
            codomain = argument.getExpression();
          } else {
            if (argument.getExpression() instanceof ConcreteReferenceExpression) {
              ConcreteParameter param = argFactory.param(Collections.singletonList(((ConcreteReferenceExpression) argument.getExpression()).getReferent()), argFactory.hole());
              parameters.add(argument.isExplicit() ? param : param.implicit());
            } else {
              ConcreteParameter param = Utils.expressionToParameter(argument.getExpression(), resolver, argFactory);
              if (param == null) {
                return null;
              }
              parameters.add(argument.isExplicit() ? param : param.implicit());
            }
          }
        } else {
          List<ArendRef> refs = Utils.getRefs(argument.getExpression(), resolver);
          if (refs == null) {
            return null;
          }
          ConcreteParameter param = argFactory.param(refs, argFactory.hole());
          parameters.add(argument.isExplicit() ? param : param.implicit());
        }
      } else if (argument.isExplicit()) {
        ConcreteParameter param = Utils.expressionToParameter(argument.getExpression(), resolver, argFactory);
        if (param == null) {
          return null;
        }
        parameters.add(param);
      } else {
        List<ArendRef> refs = Utils.getTuplesOfRefs(argument.getExpression(), resolver);
        if (refs == null) {
          return null;
        }
        parameters.add(argFactory.param(refs, argFactory.hole()));
      }
    }

    return factory.app(contextData.getReferenceExpression(), true, Collections.singletonList(resolver.resolve(codomain != null ? factory.pi(parameters, codomain) : factory.sigma(parameters))));
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
      List<ConcreteParameter> varParams;
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
              if (!types[0].reportIfError(typechecker.getErrorReporter(), cType)) {
                typechecker.getErrorReporter().report(new TypeMismatchError(DocFactory.text("\\Type"), types[0], cType));
              }
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
        List<CoreParameter> piParams = new ArrayList<>();
        CoreExpression cod = type.getPiParameters(piParams);
        if (!(cod instanceof CoreUniverseExpression)) {
          typechecker.getErrorReporter().report(new TypeMismatchError(DocFactory.text("_ -> \\Type"), type, cType));
          return null;
        }
        refs = null;
        List<ArendRef> sigmaRefs = new ArrayList<>(param.getRefList().size());
        List<? extends ArendRef> paramRefList = param.getRefList();
        if (param.getRefList().isEmpty() || param.getRefList().size() == 1 && param.getRefList().get(0) == null) {
          paramRefList = new ArrayList<>(piParams.size());
          for (CoreParameter ignored : piParams) {
            paramRefList.add(null);
          }
        }
        int i = 0;
        for (ArendRef ref : paramRefList) {
          sigmaRefs.add(ref != null ? ref : factory.local(ext.renamerFactory.getNameFromType(piParams.get(i % piParams.size()).getTypeExpr(), null)));
          i++;
        }
        if (sigmaRefs.size() % piParams.size() != 0) {
          typechecker.getErrorReporter().report(new TypecheckingError("Expected (" + piParams.size() + " * n) parameters", param));
          return null;
        }

        varParams = new ArrayList<>(piParams.size());
        int j = 0;
        for (CoreParameter piParam : piParams) {
          List<ArendRef> curRef = new ArrayList<>();
          for (i = j; i < sigmaRefs.size(); i += piParams.size()) {
            curRef.add(sigmaRefs.get(i));
          }
          ConcreteParameter varParam = produceParam(param.isExplicit(), curRef, factory.withData(cType.getData()).core(piParam.getTypedType()), null);
          sigmaParams.add(varParam);
          varParams.add(varParam);
          j++;
        }
        i = 0;
        while (i < sigmaRefs.size()) {
          List<ConcreteArgument> args = new ArrayList<>(piParams.size());
          for (CoreParameter piParam : piParams) {
            args.add(factory.arg(factory.ref(sigmaRefs.get(i++)), piParam.isExplicit()));
          }
          sigmaParams.add(produceParam(true, null, factory.app(aType, args), null));
        }

        j = 0;
        for (CoreParameter ignored : piParams) {
          for (i = j; i < paramRefList.size(); i += piParams.size()) {
            ArendRef ref = paramRefList.get(i);
            arguments.add(ref == null ? null : factory.ref(ref));
          }
          j++;
        }
      } else if (type instanceof CoreClassCallExpression && ((CoreClassCallExpression) type).getDefinition() == ext.prelude.getDArray()) {
        refs = new ArrayList<>(param.getRefList().size());
        for (ArendRef ignored : param.getRefList()) {
          refs.add(factory.local("j" + (arrayIndex == 0 ? "" : arrayIndex)));
          arrayIndex++;
        }
        ConcreteParameter varParam = produceParam(param.isExplicit(), refs, factory.app(factory.ref(ext.prelude.getFin().getRef()), true, Collections.singletonList(factory.app(factory.ref(ext.prelude.getArrayLength().getRef()), false, Collections.singletonList(aType)))), param.getData());
        varParams = Collections.singletonList(varParam);
        sigmaParams.add(varParam);

        for (ArendRef ref : refs) {
          arguments.add(factory.ref(ref));
        }
      } else {
        refs = null;
        varParams = Collections.singletonList(factory.withData(param.getData()).param(param.isExplicit(), param.getRefList(), factory.withData(cType.getData()).core(typedType)));
        sigmaParams.add(produceParam(param.isExplicit(), param.getRefList(), aType, null));

        for (ArendRef ref : param.getRefList()) {
          arguments.add(ref == null ? null : factory.ref(ref));
        }
      }

      if (parameters.size() == 1) {
        return getResult();
      }

      return typechecker.withFreeBindings(new FreeBindingsModifier().addParams(varParams), tc -> {
        List<? extends ConcreteParameter> newParams = parameters.subList(1, parameters.size());
        int newAbstracted = abstracted + param.getNumberOfParameters();
        if (refs == null) {
          return processParameters(newParams, newAbstracted, tc);
        }
        List<Pair<ArendRef, CoreBinding>> list = new ArrayList<>(refs.size());
        for (int i = 0; i < refs.size(); i++) {
          TypedExpression result = tc.typecheck(factory.app(factory.ref(ext.prelude.getArrayIndex().getRef()), true, Arrays.asList(factory.withData(cType.getData()).core(typedType), factory.ref(refs.get(i)))), null);
          if (result == null) return null;
          ArendRef ref = param.getRefList().get(i);
          list.add(new Pair<>(ref, result.makeEvaluatingBinding(ref != null ? ref.getRefName() : ext.renamerFactory.getNameFromType(result.getType(), null))));
        }
        return tc.withFreeBindings(new FreeBindingsModifier().addRef(list), tc2 -> processParameters(newParams, newAbstracted, tc2));
      });
    }

    private ConcreteExpression getResult() {
      if (kind != Kind.PI) {
        return kind == Kind.TRUNCATED ? factory.app(factory.ref(ext.TruncP.getRef()), true, factory.sigma(sigmaParams)) : factory.sigma(sigmaParams);
      }
      ConcreteExpression codomain = sigmaParams.get(sigmaParams.size() - 1).getType();
      assert codomain != null;
      return factory.pi(sigmaParams.subList(0, sigmaParams.size() - 1), codomain);
    }

    private ConcreteParameter produceParam(boolean explicit, Collection<? extends ArendRef> refs, ConcreteExpression type, Object data) {
      ConcreteFactory actualFactory = data == null ? factory : factory.withData(data);
      return refs == null ? actualFactory.param(explicit, type) : actualFactory.param(explicit, refs, type);
    }
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());
    ConcreteExpression arg = contextData.getArguments().get(0).getExpression();
    List<? extends ConcreteParameter> params;
    if (arg instanceof ConcretePiExpression) {
      List<ConcreteParameter> params1 = new ArrayList<>(((ConcretePiExpression) arg).getParameters());
      params1.add(factory.param(true, ((ConcretePiExpression) arg).getCodomain()));
      params = params1;
    } else if (arg instanceof ConcreteSigmaExpression) {
      params = ((ConcreteSigmaExpression) arg).getParameters();
    } else {
      params = Collections.singletonList(factory.param(true, arg));
    }
    ConcreteExpression result = new Processor(factory).processParameters(params, 0, typechecker);
    return result == null ? null : typechecker.typecheck(result, contextData.getExpectedType());
  }
}
