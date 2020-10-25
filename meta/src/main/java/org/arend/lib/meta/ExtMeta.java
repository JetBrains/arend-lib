package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteLamExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.*;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
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

  private void checkNoArgs(List<? extends ConcreteArgument> args, ErrorReporter errorReporter) {
    if (!args.isEmpty()) {
      errorReporter.report(new IgnoredArgumentError(args.get(0).getExpression()));
    }
  }

  private class ExtGenerator {
    private final ExpressionTypechecker typechecker;
    private final ConcreteFactory factory;
    private final ArendRef iRef;
    private final boolean isConst;

    private ExtGenerator(ExpressionTypechecker typechecker, ConcreteFactory factory, ArendRef iRef, boolean isConst) {
      this.typechecker = typechecker;
      this.factory = factory;
      this.iRef = iRef;
      this.isConst = isConst;
    }

    private ConcreteExpression generate(ConcreteExpression arg, CoreExpression type, ConcreteExpression left, ConcreteExpression right) {
      if (!isConst) throw new IllegalStateException();
      if (type instanceof CorePiExpression) {
        List<CoreParameter> piParams = new ArrayList<>();
        type = type.getPiParameters(piParams);
        List<ConcreteArgument> args = new ArrayList<>();
        List<ConcreteParameter> lamParams = new ArrayList<>();
        while (arg instanceof ConcreteLamExpression) {
          List<? extends ConcreteParameter> params = ((ConcreteLamExpression) arg).getParameters();
          for (ConcreteParameter param : params) {
            for (ArendRef ref : param.getRefList()) {
              if (ref == null) {
                typechecker.getErrorReporter().report(new TypecheckingError("Expected a named parameter", arg));
                return null;
              }
              args.add(factory.arg(factory.ref(ref), param.isExplicit()));
            }
          }
          lamParams.addAll(params);
          arg = ((ConcreteLamExpression) arg).getBody();
        }
        if (piParams.size() != args.size()) {
          typechecker.getErrorReporter().report(new TypecheckingError("Expected a lambda expression" + (piParams.size() == 1 && args.size() == 0 ? "" : piParams.size() + " parameters"), arg));
          return null;
        }

        ConcreteExpression result = generate(arg, type.normalize(NormalizationMode.WHNF), factory.app(left, args), factory.app(right, args));
        return result == null ? null : factory.lam(lamParams, result);
      }

      return factory.app(factory.ref(ext.prelude.getAt().getRef()), true, Arrays.asList(factory.typed(arg, factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(left, right))), factory.ref(iRef)));
    }
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteSourceNode marker = contextData.getMarker();
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    CoreExpression pathType = contextData.getExpectedType().normalize(NormalizationMode.WHNF);
    if (!(pathType instanceof CoreDataCallExpression && ((CoreDataCallExpression) pathType).getDefinition() == ext.prelude.getPath())) {
      errorReporter.report(new TypeMismatchError(DocFactory.text(ext.prelude.getPath().getName()), pathType, marker));
      return null;
    }

    List<? extends ConcreteArgument> args = contextData.getArguments();
    ConcreteFactory factory = ext.factory.withData(marker);
    List<? extends CoreExpression> pathArgs = ((CoreDataCallExpression) pathType).getDefCallArguments();
    CoreExpression typeFun = pathArgs.get(0).normalize(NormalizationMode.WHNF);
    CoreExpression type = typeFun.removeConstLam();
    boolean isConst = type != null;
    if (type == null) {
      CoreExpression typeType = typeFun.computeType().normalize(NormalizationMode.WHNF);
      if (typeType instanceof CorePiExpression) {
        type = ((CorePiExpression) typeType).getCodomain();
      } else {
        errorReporter.report(new TypecheckingError("Cannot infer type", marker));
        return null;
      }
    }

    CoreExpression typeType = type.computeType().normalize(NormalizationMode.WHNF);
    if (typeType instanceof CoreUniverseExpression && ((CoreUniverseExpression) typeType).getSort().isProp()) {
      checkNoArgs(args, errorReporter);
      return typechecker.typecheck(isConst
        ? factory.app(factory.ref(ext.prelude.getInProp().getRef()), true, Arrays.asList(factory.hole(), factory.hole()))
        : factory.app(factory.ref(ext.pathInProp.getRef()), true, Arrays.asList(factory.hole(), factory.hole(), factory.hole())),
        contextData.getExpectedType());
    }

    if (args.isEmpty()) {
      errorReporter.report(new MissingArgumentsError(1, marker));
      return null;
    }

    if (!isConst && !(typeFun instanceof CoreLamExpression)) {
      return typechecker.typecheck(args.get(0).getExpression(), contextData.getExpectedType());
    }

    ArendRef iRef = factory.local("i");
    CoreExpression finalType = type;
    return typechecker.typecheck(factory.app(factory.ref(ext.prelude.getPathCon().getRef()), true, Collections.singletonList(factory.lam(Collections.singletonList(factory.param(iRef)), factory.meta("ext_result", new MetaDefinition() {
      @Override
      public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        CoreExpression type;
        if (isConst) {
          type = finalType;
        } else {
          TypedExpression typed = typechecker.typecheck(factory.app(factory.core(typeFun.computeTyped()), true, Collections.singletonList(factory.ref(iRef))), null);
          if (typed == null) return null;
          type = typed.getExpression();
        }
        ConcreteExpression result = new ExtGenerator(typechecker, factory, iRef, isConst).generate(args.get(0).getExpression(), type.normalize(NormalizationMode.WHNF), factory.core(pathArgs.get(1).computeTyped()), factory.core(pathArgs.get(2).computeTyped()));
        return result == null ? null : typechecker.typecheck(result, null);
      }
    })))), contextData.getExpectedType());
  }
}
