package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.ConcretePattern;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteCaseArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.error.TypeError;
import org.arend.lib.meta.pi_tree.*;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class SimpCoeMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  @Dependency(module = "Paths")                                     public CoreFunctionDefinition transport_path_pmap;
  @Dependency(module = "Paths", name = "transport_path_pmap-right") public CoreFunctionDefinition transport_path_pmap_right;

  public SimpCoeMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  private interface Spec {
    ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight, ConcreteExpression argument);
  }

  private class EqualitySpec implements Spec {
    final CoreExpression leftFunc;
    final CoreExpression rightFunc;
    final boolean isLeftConst;

    private EqualitySpec(CoreParameter lamParam, CoreFunCallExpression equality, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
      if (equality.getDefCallArguments().get(1).findFreeBinding(lamParam.getBinding())) {
        leftFunc = typechecker.makeLambda(Collections.singletonList(lamParam), equality.getDefCallArguments().get(1), marker);
        isLeftConst = false;
      } else {
        leftFunc = equality.getDefCallArguments().get(1);
        isLeftConst = true;
      }
      rightFunc = typechecker.makeLambda(Collections.singletonList(lamParam), equality.getDefCallArguments().get(2), marker);
    }

    @Override
    public ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight, ConcreteExpression argument) {
      return factory.app(factory.ref((isLeftConst ? transport_path_pmap_right : transport_path_pmap).getRef()), true, Arrays.asList(factory.core(leftFunc.computeTyped()), factory.core(rightFunc.computeTyped()), transportPathArg, factory.core(transportValueArg.computeTyped()), factory.core(eqRight.computeTyped()), argument));
    }
  }

  private class PiSpec implements Spec {
    final PiTreeMaker piTreeMaker;
    final PiTreeRoot piTree;
    final List<ConcreteLetClause> letClauses;

    PiSpec(PiTreeMaker piTreeMaker, PiTreeRoot piTree, List<ConcreteLetClause> letClauses) {
      this.piTreeMaker = piTreeMaker;
      this.piTree = piTree;
      this.letClauses = letClauses;
    }

    @Override
    public ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight, ConcreteExpression argument) {
      List<ConcreteCaseArgument> caseArgs = new ArrayList<>(4);
      List<ConcretePattern> casePatterns = new ArrayList<>(4);
      ArendRef rightRef = factory.local("r");
      List<ConcreteExpression> rightRefs = Collections.singletonList(factory.ref(rightRef));
      caseArgs.add(factory.caseArg(transportRightArg, rightRef, null));

      ArendRef pathRef = factory.local("q");
      List<PathExpression> pathRefs = Collections.singletonList(new PathExpression(factory.ref(pathRef)));
      caseArgs.add(factory.caseArg(transportPathArg, pathRef, factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(transportLeftArg, factory.ref(rightRef)))));

      casePatterns.add(factory.refPattern(null, null));
      casePatterns.add(factory.conPattern(ext.prelude.getIdp().getRef()));

      ArendRef rightFunRef = factory.local("g");
      caseArgs.add(factory.caseArg(factory.core(eqRight.computeTyped()), rightFunRef, piTreeMaker.makeConcrete(piTree, true, rightRefs)));
      ConcreteExpression concreteValueArg = factory.core(transportValueArg.computeTyped());
      caseArgs.add(factory.caseArg(argument, null, piTreeMaker.makeArgType(piTree, true, Collections.singletonList(transportLeftArg), rightRefs, pathRefs, concreteValueArg, factory.ref(rightFunRef))));

      ArendRef lastCaseRef = factory.local("a");
      casePatterns.add(factory.refPattern(null, null));
      casePatterns.add(factory.refPattern(lastCaseRef, null));

      ConcreteExpression caseResultType = factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(piTreeMaker.makeCoe(piTree, true, pathRefs, concreteValueArg), factory.ref(rightFunRef)));
      ConcreteExpression result = factory.caseExpr(false, caseArgs, caseResultType, null, factory.clause(casePatterns, factory.app(factory.meta("ext", ext.extsMeta), true, Collections.singletonList(factory.ref(lastCaseRef)))));
      return letClauses.isEmpty() ? result : factory.letExpr(false, false, letClauses, result);
    }
  }

  private class PiArgsSpec implements Spec {
    final List<CoreExpression> arguments;
    final CoreLamExpression transportLam;
    final List<CoreParameter> parameters;
    final CoreExpression codomain;

    PiArgsSpec(List<CoreExpression> arguments, CoreLamExpression transportLam, List<CoreParameter> parameters, CoreExpression codomain) {
      this.arguments = arguments;
      this.transportLam = transportLam;
      this.parameters = parameters;
      this.codomain = codomain;
    }

    @Override
    public ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight, ConcreteExpression argument) {
      List<ConcreteLetClause> clauses = new ArrayList<>(1);
      ConcreteExpression concreteValueArg;
      if (transportValueArg instanceof CoreReferenceExpression) {
        concreteValueArg = factory.core(transportValueArg.computeTyped());
      } else {
        ArendRef letRef = factory.local("f");
        clauses.add(factory.letClause(letRef, Collections.emptyList(), null, factory.core(transportValueArg.computeTyped())));
        concreteValueArg = factory.ref(letRef);
      }

      ArendRef jRef = factory.local("q");
      ArendRef transportRef = factory.local("z");
      List<ConcreteExpression> jTypeLeftArgs = new ArrayList<>(Arrays.asList(factory.core(transportLam.computeTyped()), factory.ref(jRef), concreteValueArg));
      List<SubstitutionPair> substitution = new ArrayList<>();
      substitution.add(new SubstitutionPair(transportLam.getParameters().getBinding(), factory.ref(transportRef)));
      List<ConcreteArgument> lastArgs = new ArrayList<>();
      for (int i = 0; i < arguments.size(); i++) {
        ConcreteExpression cArg = factory.core(arguments.get(i).computeTyped());
        jTypeLeftArgs.add(cArg);
        lastArgs.add(factory.arg(cArg, parameters.get(i).isExplicit()));
        substitution.add(new SubstitutionPair(parameters.get(i).getBinding(), cArg));
      }

      ConcreteExpression transportLam = factory.lam(Collections.singletonList(factory.param(transportRef)), factory.meta("transport_arg", new MetaDefinition() {
        @Override
        public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          CoreExpression result = typechecker.substitute(codomain, null, substitution);
          return result == null ? null : result.computeTyped();
        }
      }));
      ConcreteExpression jTypeLeft = factory.app(factory.ref(ext.transport.getRef()), true, jTypeLeftArgs);
      ConcreteExpression jTypeRight = factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(transportLam, factory.ref(jRef), factory.app(concreteValueArg, lastArgs)));
      ConcreteExpression jLam = factory.lam(Arrays.asList(factory.param(null), factory.param(jRef)), factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(jTypeLeft, jTypeRight)));
      ConcreteExpression jExpr = factory.app(factory.ref(ext.Jl.getRef()), true, Arrays.asList(jLam, factory.ref(ext.prelude.getIdp().getRef()), transportPathArg));
      ConcreteExpression result = factory.app(factory.ref(ext.concat.getRef()), true, Arrays.asList(jExpr, argument));
      return clauses.isEmpty() ? result : factory.letExpr(false, false, clauses, result);
    }
  }

  private Spec getSpec(CoreExpression arg, ExpressionTypechecker typechecker, ConcreteSourceNode marker, ConcreteFactory factory, List<CoreExpression> args) {
    arg = arg.normalize(NormalizationMode.WHNF);
    if (!(arg instanceof CoreLamExpression)) {
      return null;
    }

    CoreLamExpression lam = (CoreLamExpression) arg;
    if (lam.getParameters().getNext().hasNext()) {
      return null;
    }

    CoreExpression body = lam.getBody().getUnderlyingExpression();
    if (body instanceof CoreFunCallExpression && ((CoreFunCallExpression) body).getDefinition() == ext.prelude.getEquality()) {
      return new EqualitySpec(lam.getParameters(), (CoreFunCallExpression) body, typechecker, marker);
    }

    body = body.normalize(NormalizationMode.WHNF);

    if (!args.isEmpty() && !(body instanceof CorePiExpression)) {
      return null;
    }

    if (body instanceof CorePiExpression) {
      if (args.isEmpty()) {
        List<ConcreteLetClause> letClauses = new ArrayList<>();
        PiTreeMaker piTreeMaker = new PiTreeMaker(ext, typechecker, factory, letClauses);
        PiTreeRoot piTree = piTreeMaker.make(body, Collections.singletonList(lam.getParameters()));
        return piTree.isNonDependent() ? null : new PiSpec(piTreeMaker, piTree, letClauses);
      } else {
        int s = 0;
        List<CoreParameter> parameters = new ArrayList<>();
        while (true) {
          CoreParameter param = ((CorePiExpression) body).getParameters();
          if (param.getTypeExpr().findFreeBinding(lam.getParameters().getBinding())) {
            return null;
          }

          int n = 0;
          for (; param.hasNext() && s < args.size(); param = param.getNext(), n++, s++) {
            parameters.add(param);
          }
          if (s == args.size()) {
            body = param.hasNext() ? ((CorePiExpression) body).dropParameters(n) : ((CorePiExpression) body).getCodomain();
            break;
          }
          body = ((CorePiExpression) body).getCodomain();
        }

        return new PiArgsSpec(args, lam, parameters, body);
      }
    }

    CoreFunCallExpression equality = body.toEquality();
    if (equality != null ) {
      return new EqualitySpec(lam.getParameters(), equality, typechecker, marker);
    }

    return null;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    CoreFunCallExpression equality = Utils.toEquality(contextData.getExpectedType(), typechecker.getErrorReporter(), contextData.getMarker());
    if (equality == null) return null;
    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());

    CoreExpression leftExpr = equality.getDefCallArguments().get(1).getUnderlyingExpression();
    List<CoreExpression> arguments = new ArrayList<>();
    while (true) {
      if (!(leftExpr instanceof CoreAppExpression || leftExpr instanceof CoreFunCallExpression && (((CoreFunCallExpression) leftExpr).getDefinition() == ext.prelude.getCoerce() || ((CoreFunCallExpression) leftExpr).getDefinition() == ext.transport))) {
        leftExpr = leftExpr.normalize(NormalizationMode.WHNF);
      }
      if (!(leftExpr instanceof CoreAppExpression)) {
        break;
      }
      arguments.add(((CoreAppExpression) leftExpr).getArgument());
      leftExpr = ((CoreAppExpression) leftExpr).getFunction().getUnderlyingExpression();
    }
    Collections.reverse(arguments);

    if (leftExpr instanceof CoreFunCallExpression && ((CoreFunCallExpression) leftExpr).getDefinition() == ext.transport) {
      var transportArgs = ((CoreFunCallExpression) leftExpr).getDefCallArguments();
      Spec spec = getSpec(transportArgs.get(1), typechecker, contextData.getMarker(), factory, arguments);
      if (spec != null) {
        return typechecker.typecheck(spec.make(factory, factory.core(transportArgs.get(2).computeTyped()), factory.core(transportArgs.get(3).computeTyped()), factory.core(transportArgs.get(4).computeTyped()), transportArgs.get(5), equality.getDefCallArguments().get(2), contextData.getArguments().get(0).getExpression()), contextData.getExpectedType());
      }
    } else {
      if (leftExpr instanceof CoreFunCallExpression && ((CoreFunCallExpression) leftExpr).getDefinition() == ext.prelude.getCoerce()) {
        var coeArgs = ((CoreFunCallExpression) leftExpr).getDefCallArguments();
        CoreExpression lastArg = coeArgs.get(2).normalize(NormalizationMode.WHNF);
        if (lastArg instanceof CoreConCallExpression && ((CoreConCallExpression) lastArg).getDefinition() == ext.prelude.getRight()) {
          Spec spec = getSpec(coeArgs.get(0), typechecker, contextData.getMarker(), factory, arguments);
          if (spec != null) {
            ArendRef iRef = factory.local("i");
            return typechecker.typecheck(spec.make(factory, factory.ref(ext.prelude.getLeft().getRef()), factory.ref(ext.prelude.getRight().getRef()), factory.app(factory.ref(ext.prelude.getPathCon().getRef()), true, Collections.singletonList(factory.lam(Collections.singletonList(factory.param(iRef)), factory.ref(iRef)))), coeArgs.get(1), equality.getDefCallArguments().get(2), contextData.getArguments().get(0).getExpression()), contextData.getExpectedType());
          }
        }
      }
    }

    typechecker.getErrorReporter().report(new TypeError("Type is not supported", contextData.getExpectedType(), contextData.getMarker()));
    return null;
  }
}
