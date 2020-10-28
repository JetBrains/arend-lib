package org.arend.lib.meta;

import org.arend.ext.FreeBindingsModifier;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.concrete.expr.ConcreteTupleExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.error.*;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.error.TypeError;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class ExtMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public ExtMeta(StdExtension ext) {
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
  public boolean requireExpectedType() {
    return true;
  }

  private class ExtGenerator {
    private final ExpressionTypechecker typechecker;
    private final ConcreteFactory factory;
    private final ConcreteSourceNode marker;
    private final ArendRef iRef;

    private ExtGenerator(ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteSourceNode marker, ArendRef iRef) {
      this.typechecker = typechecker;
      this.factory = factory;
      this.marker = marker;
      this.iRef = iRef;
    }

    private ConcreteExpression applyAt(ConcreteExpression arg) {
      return factory.app(factory.ref(ext.prelude.getAt().getRef()), true, Arrays.asList(arg, factory.ref(iRef)));
    }

    private TypedExpression hidingIRef(ConcreteExpression expr, CoreExpression type) {
      return typechecker.withFreeBindings(new FreeBindingsModifier().remove(typechecker.getFreeBinding(iRef)), tc -> tc.typecheck(expr, type));
    }

    private ConcreteExpression makeCoeLambda(CoreSigmaExpression sigma, CoreBinding paramBinding, Set<CoreBinding> used, Map<CoreBinding, ConcreteExpression> sigmaRefs, ConcreteFactory factory) {
      ArendRef coeRef = factory.local("i");
      return factory.lam(Collections.singletonList(factory.param(coeRef)), factory.meta("ext_coe", new MetaDefinition() {
        @Override
        public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          List<SubstitutionPair> substitution = new ArrayList<>();
          for (CoreParameter param = sigma.getParameters(); param.getBinding() != paramBinding; param = param.getNext()) {
            if (used == null || used.contains(param.getBinding())) {
              substitution.add(new SubstitutionPair(param.getBinding(), factory.app(factory.ref(ext.prelude.getAt().getRef()), true, Arrays.asList(sigmaRefs.get(param.getBinding()), factory.ref(coeRef)))));
            }
          }
          CoreExpression result = typechecker.substitute(paramBinding.getTypeExpr(), null, substitution);
          return result == null ? null : result.computeTyped();
        }
      }));
    }

    private ConcreteExpression generate(ConcreteExpression arg, CoreExpression type, ConcreteExpression left, ConcreteExpression right) {
      if (type instanceof CorePiExpression) {
        List<CoreParameter> piParams = new ArrayList<>();
        type.getPiParameters(piParams);
        List<ConcreteParameter> concretePiParams = new ArrayList<>();
        List<ConcreteParameter> concreteLamParams = new ArrayList<>();
        List<ConcreteArgument> args = new ArrayList<>();
        List<SubstitutionPair> substitution = new ArrayList<>();
        for (int i = 0; i < piParams.size(); i++) {
          CoreParameter piParam = piParams.get(i);
          ArendRef ref = factory.local(ext.renamerFactory.getNameFromBinding(piParam.getBinding(), null));
          int finalI = i;
          concretePiParams.add(factory.param(piParam.isExplicit(), Collections.singletonList(ref), factory.meta("ext_param", new MetaDefinition() {
            @Override
            public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
              CoreExpression paramType = typechecker.substitute(piParam.getTypeExpr(), null, substitution.subList(0, finalI));
              return paramType == null ? null : paramType.computeTyped();
            }
          })));
          concreteLamParams.add(factory.param(piParam.isExplicit(), ref));
          ConcreteExpression refExpr = factory.ref(ref);
          args.add(factory.arg(refExpr, piParam.isExplicit()));
          substitution.add(new SubstitutionPair(piParam.getBinding(), refExpr));
        }

        TypedExpression piEqType = typechecker.typecheck(factory.pi(concretePiParams, factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(factory.app(left, args), factory.app(right, args)))), null);
        if (piEqType == null) return null;
        TypedExpression result = hidingIRef(arg, piEqType.getExpression());
        return result == null ? null : factory.lam(concreteLamParams, applyAt(factory.app(factory.core(result), args)));
      }

      if (type instanceof CoreSigmaExpression) {
        CoreSigmaExpression sigma = (CoreSigmaExpression) type;
        Set<CoreBinding> bindings = new HashSet<>();
        Set<CoreBinding> dependentBindings = new HashSet<>();
        List<ConcreteParameter> sigmaParams = new ArrayList<>();
        Map<CoreBinding, ConcreteExpression> sigmaRefs = new HashMap<>();
        ConcreteExpression lastSigmaParam = null;
        Set<CoreBinding> propBindings = new HashSet<>();
        Set<CoreBinding> totalUsed = new HashSet<>();
        List<Set<CoreBinding>> usedList = new ArrayList<>();
        int i = 0;
        for (CoreParameter param = sigma.getParameters(); param.hasNext(); param = param.getNext(), i++) {
          Set<CoreBinding> used = new HashSet<>();
          CoreBinding paramBinding = param.getBinding();
          boolean isProp = isProp(paramBinding.getTypeExpr());
          if (isProp) {
            propBindings.add(paramBinding);
          }
          if (!bindings.isEmpty()) {
            if (param.getTypeExpr().processSubexpression(e -> {
              if (!(e instanceof CoreReferenceExpression)) {
                return CoreExpression.FindAction.CONTINUE;
              }
              CoreBinding binding = ((CoreReferenceExpression) e).getBinding();
              if (bindings.contains(binding)) {
                if (!isProp) {
                  if (dependentBindings.contains(binding)) {
                    return CoreExpression.FindAction.STOP;
                  }
                  dependentBindings.add(paramBinding);
                }
                used.add(binding);
              }
              return CoreExpression.FindAction.CONTINUE;
            })) {
              typechecker.getErrorReporter().report(new TypecheckingError("\\Sigma types with more than two level of dependencies are not supported", marker));
              return null;
            }
          }
          bindings.add(paramBinding);
          totalUsed.addAll(used);
          usedList.add(used);

          ArendRef sigmaRef = factory.local("p" + (i + 1));
          sigmaRefs.put(paramBinding, factory.ref(sigmaRef));
          ConcreteExpression leftExpr = factory.proj(left, i);
          if (!isProp) {
            if (dependentBindings.contains(paramBinding)) {
              if (used.size() > 1) {
                leftExpr = factory.app(factory.ref(ext.prelude.getCoerce().getRef()), true, Arrays.asList(makeCoeLambda(sigma, paramBinding, used, sigmaRefs, factory), leftExpr, factory.ref(ext.prelude.getRight().getRef())));
              } else {
                CoreBinding binding = used.iterator().next();
                ArendRef transportRef = factory.local(ext.renamerFactory.getNameFromBinding(binding, null));
                leftExpr = factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(factory.lam(Collections.singletonList(factory.param(transportRef)), factory.meta("ext_transport", new MetaDefinition() {
                  @Override
                  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
                    CoreExpression result = typechecker.substitute(paramBinding.getTypeExpr(), null, Collections.singletonList(new SubstitutionPair(binding, factory.ref(transportRef))));
                    return result == null ? null : result.computeTyped();
                  }
                })), sigmaRefs.get(binding), leftExpr));
              }
            }
            lastSigmaParam = factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(leftExpr, factory.proj(right, i)));
            sigmaParams.add(factory.param(true, Collections.singletonList(sigmaRef), lastSigmaParam));
          }
        }

        TypedExpression sigmaEqType = typechecker.typecheck(sigmaParams.size() == 1 ? lastSigmaParam : factory.sigma(sigmaParams), null);
        if (sigmaEqType == null) return null;
        TypedExpression result = hidingIRef(arg, sigmaEqType.getExpression());
        if (result == null) return null;

        ArendRef letRef;
        ConcreteExpression concreteTuple;
        CoreExpression resultExpr = result.getExpression().getUnderlyingExpression();
        if (resultExpr instanceof CoreTupleExpression || resultExpr instanceof CoreReferenceExpression) {
          letRef = null;
          concreteTuple = factory.core(result);
        } else {
          letRef = factory.local("h");
          concreteTuple = factory.ref(letRef);
        }

        List<ConcreteLetClause> letClauses = new ArrayList<>();
        if (letRef != null) {
          letClauses.add(factory.letClause(letRef, Collections.emptyList(), null, factory.core(result)));
        }

        List<ConcreteExpression> fields = new ArrayList<>();
        Map<CoreBinding, ConcreteExpression> fieldsMap = new HashMap<>();
        i = 0;
        for (CoreParameter param = sigma.getParameters(); param.hasNext(); param = param.getNext(), i++) {
          ConcreteExpression field;
          CoreBinding paramBinding = param.getBinding();
          boolean useLet;
          if (propBindings.contains(paramBinding)) {
            field = factory.app(factory.ref(ext.pathInProp.getRef()), true, Arrays.asList(makeCoeLambda(sigma, paramBinding, usedList.get(i), fieldsMap, factory), factory.hole(), factory.hole()));
            useLet = true;
          } else {
            ConcreteExpression proj = sigmaParams.size() == 1 ? concreteTuple : factory.proj(concreteTuple, i);
            boolean isDependent = dependentBindings.contains(paramBinding);
            field = isDependent ? factory.app(factory.ref(ext.pathOver.getRef()), true, Collections.singletonList(proj)) : proj;
            useLet = isDependent || !((sigmaParams.size() != 1 || concreteTuple instanceof ConcreteReferenceExpression) && (sigmaParams.size() == 1 || concreteTuple instanceof ConcreteReferenceExpression || concreteTuple instanceof ConcreteTupleExpression && i < ((ConcreteTupleExpression) concreteTuple).getFields().size() && ((ConcreteTupleExpression) concreteTuple).getFields().get(i) instanceof ConcreteReferenceExpression));
          }
          if (useLet && totalUsed.contains(paramBinding)) {
            ArendRef argLetRef = factory.local("h" + (i + 1));
            letClauses.add(factory.letClause(argLetRef, Collections.emptyList(), null, field));
            field = factory.ref(argLetRef);
          }
          fields.add(applyAt(field));
          fieldsMap.put(paramBinding, field);
        }

        ConcreteExpression concreteResult = factory.tuple(fields);
        return letClauses.isEmpty() ? concreteResult : factory.letExpr(false, letClauses, concreteResult);
      }

      typechecker.getErrorReporter().report(new TypeError("Cannot apply extensionality", type, marker));
      return null;
    }
  }

  private static boolean isProp(CoreExpression type) {
    CoreExpression typeType = type.computeType().normalize(NormalizationMode.WHNF);
    return typeType instanceof CoreUniverseExpression && ((CoreUniverseExpression) typeType).getSort().isProp();
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteSourceNode marker = contextData.getMarker();
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    CoreFunCallExpression equality = Utils.toEquality(contextData.getExpectedType(), errorReporter, marker);
    if (equality == null) return null;

    List<? extends ConcreteArgument> args = contextData.getArguments();
    ConcreteFactory factory = ext.factory.withData(marker);
    CoreExpression type = equality.getDefCallArguments().get(0);
    if (isProp(type)) {
      if (!args.isEmpty()) {
        errorReporter.report(new IgnoredArgumentError(args.get(0).getExpression()));
      }
      return typechecker.typecheck(factory.app(factory.ref(ext.prelude.getInProp().getRef()), true, Arrays.asList(factory.hole(), factory.hole())), contextData.getExpectedType());
    }

    if (args.isEmpty()) {
      errorReporter.report(new MissingArgumentsError(1, marker));
      return null;
    }

    ArendRef iRef = factory.local("i");
    return typechecker.typecheck(factory.app(factory.ref(ext.prelude.getPathCon().getRef()), true, Collections.singletonList(factory.lam(Collections.singletonList(factory.param(iRef)), factory.meta("ext_result", new MetaDefinition() {
      @Override
      public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        CoreExpression normType = type.normalize(NormalizationMode.WHNF);
        ConcreteExpression result = new ExtGenerator(typechecker, factory, marker, iRef).generate(args.get(0).getExpression(), normType, factory.core(equality.getDefCallArguments().get(1).computeTyped()), factory.core(equality.getDefCallArguments().get(2).computeTyped()));
        return result == null ? null : typechecker.typecheck(result, normType);
      }
    })))), contextData.getExpectedType());
  }
}
