package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteTupleExpression;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.error.*;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

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
    private final ArendRef iRef;

    private ExtGenerator(ExpressionTypechecker typechecker, ConcreteFactory factory, ArendRef iRef) {
      this.typechecker = typechecker;
      this.factory = factory;
      this.iRef = iRef;
    }

    private ConcreteExpression applyAt(ConcreteExpression arg) {
      return factory.app(factory.ref(ext.prelude.getAt().getRef()), true, Arrays.asList(arg, factory.ref(iRef)));
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
        TypedExpression result = typechecker.typecheck(arg, piEqType.getExpression());
        return result == null ? null : factory.lam(concreteLamParams, applyAt(factory.app(factory.core(result), args)));
      }

      return applyAt(factory.typed(arg, factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(left, right))));
    }
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
    CoreExpression typeType = type.computeType().normalize(NormalizationMode.WHNF);
    if (typeType instanceof CoreUniverseExpression && ((CoreUniverseExpression) typeType).getSort().isProp()) {
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
        ConcreteExpression result = new ExtGenerator(typechecker, factory, iRef).generate(args.get(0).getExpression(), type.normalize(NormalizationMode.WHNF), factory.core(equality.getDefCallArguments().get(1).computeTyped()), factory.core(equality.getDefCallArguments().get(2).computeTyped()));
        return result == null ? null : typechecker.typecheck(result, null);
      }
    })))), contextData.getExpectedType());
  }
}
