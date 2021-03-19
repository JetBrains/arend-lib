package org.arend.lib.meta;

import org.arend.ext.concrete.*;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.error.FieldsImplementationError;
import org.arend.ext.error.RedundantCoclauseError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.error.SubclassError;
import org.arend.lib.error.TypeError;
import org.arend.lib.meta.pi_tree.*;
import org.arend.lib.meta.util.SubstitutionMeta;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

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

  @Override
  public boolean allowCoclauses() {
    return true;
  }

  private static abstract class Spec {
    final List<ConcreteLetClause> letClauses;
    final ConcreteExpression argument;

    protected Spec(List<ConcreteLetClause> letClauses, ConcreteExpression concreteArg) {
      this.letClauses = letClauses;
      this.argument = concreteArg;
    }

    abstract ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight);

    ConcreteExpression makeConcreteValueArg(CoreExpression valueArg, ConcreteFactory factory) {
      if (valueArg instanceof CoreReferenceExpression) {
        return factory.core(valueArg.computeTyped());
      } else {
        ArendRef letRef = factory.local("f");
        letClauses.add(factory.letClause(letRef, Collections.emptyList(), null, factory.core(valueArg.computeTyped())));
        return factory.ref(letRef);
      }
    }
  }

  private static class ErrorSpec extends Spec {
    protected ErrorSpec() {
      super(Collections.emptyList(), null);
    }

    @Override
    ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight) {
      return null;
    }
  }

  private class EqualitySpec extends Spec {
    final CoreExpression leftFunc;
    final CoreExpression rightFunc;
    final boolean isLeftConst;

    private EqualitySpec(CoreParameter lamParam, CoreFunCallExpression equality, ExpressionTypechecker typechecker, ConcreteSourceNode marker, ConcreteExpression concreteArg) {
      super(Collections.emptyList(), concreteArg);
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
    public ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight) {
      return factory.app(factory.ref((isLeftConst ? transport_path_pmap_right : transport_path_pmap).getRef()), true, Arrays.asList(factory.core(leftFunc.computeTyped()), factory.core(rightFunc.computeTyped()), transportPathArg, factory.core(transportValueArg.computeTyped()), factory.core(eqRight.computeTyped()), argument));
    }
  }

  private class PiSpec extends Spec {
    final PiTreeMaker piTreeMaker;
    final PiTreeRoot piTree;

    PiSpec(PiTreeMaker piTreeMaker, PiTreeRoot piTree, List<ConcreteLetClause> letClauses, ConcreteExpression concreteArg) {
      super(letClauses, concreteArg);
      this.piTreeMaker = piTreeMaker;
      this.piTree = piTree;
    }

    @Override
    public ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight) {
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
      ConcreteExpression concreteValueArg = makeConcreteValueArg(transportValueArg, factory);
      caseArgs.add(factory.caseArg(argument, null, piTreeMaker.makeArgType(piTree, true, Collections.singletonList(transportLeftArg), rightRefs, pathRefs, concreteValueArg, factory.ref(rightFunRef))));

      ArendRef lastCaseRef = factory.local("a");
      casePatterns.add(factory.refPattern(null, null));
      casePatterns.add(factory.refPattern(lastCaseRef, null));

      ConcreteExpression caseResultType = factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(piTreeMaker.makeCoe(piTree, true, pathRefs, concreteValueArg), factory.ref(rightFunRef)));
      ConcreteExpression result = factory.caseExpr(false, caseArgs, caseResultType, null, factory.clause(casePatterns, factory.app(factory.meta("ext", ext.extsMeta), true, Collections.singletonList(factory.ref(lastCaseRef)))));
      return letClauses.isEmpty() ? result : factory.letExpr(false, false, letClauses, result);
    }
  }

  private class PiArgsSpec extends Spec {
    final List<CoreExpression> arguments;
    final CoreLamExpression transportLam;
    final List<CoreParameter> parameters;
    final CoreExpression codomain;

    PiArgsSpec(List<CoreExpression> arguments, CoreLamExpression transportLam, List<CoreParameter> parameters, CoreExpression codomain, ConcreteExpression concreteArg) {
      super(new ArrayList<>(), concreteArg);
      this.arguments = arguments;
      this.transportLam = transportLam;
      this.parameters = parameters;
      this.codomain = codomain;
    }

    @Override
    public ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight) {
      ConcreteExpression concreteValueArg = makeConcreteValueArg(transportValueArg, factory);
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

      ConcreteExpression rightTransportLam = factory.lam(Collections.singletonList(factory.param(transportRef)), factory.meta("transport_arg", new SubstitutionMeta(codomain, substitution)));
      ConcreteExpression jTypeLeft = factory.app(factory.ref(ext.transport.getRef()), true, jTypeLeftArgs);
      ConcreteExpression jTypeRight = factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(rightTransportLam, factory.ref(jRef), factory.app(concreteValueArg, lastArgs)));
      ConcreteExpression jLam = factory.lam(Arrays.asList(factory.param(null), factory.param(jRef)), factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(jTypeLeft, jTypeRight)));
      ConcreteExpression jExpr = factory.app(factory.ref(ext.Jl.getRef()), true, Arrays.asList(jLam, factory.ref(ext.prelude.getIdp().getRef()), transportPathArg));
      ConcreteExpression result = factory.app(factory.ref(ext.concat.getRef()), true, Arrays.asList(jExpr, argument));
      return letClauses.isEmpty() ? result : factory.letExpr(false, false, letClauses, result);
    }
  }

  private class SigmaSpec extends Spec {
    final CoreLamExpression transportLam;
    final List<CoreExpression> sigmaParamTypes;
    final List<CoreClassField> fields;
    final List<Integer> indices;

    SigmaSpec(CoreLamExpression transportLam, List<CoreExpression> sigmaParamTypes, List<CoreClassField> fields, List<Integer> indices, ConcreteExpression concreteArg) {
      super(new ArrayList<>(), concreteArg);
      this.transportLam = transportLam;
      this.sigmaParamTypes = sigmaParamTypes;
      this.fields = fields;
      this.indices = indices;
    }

    ConcreteExpression proj(ConcreteExpression expr, int i, ConcreteFactory factory) {
      return fields == null ? factory.proj(expr, indices.get(i)) : factory.app(factory.ref(fields.get(i).getRef()), false, Collections.singletonList(expr));
    }

    @Override
    ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight) {
      ArendRef jLamRef1 = factory.local("a''");
      ArendRef jLamRef2 = factory.local("q");
      ArendRef jPiRef = factory.local("s'");
      ArendRef typeRef = factory.local("T");
      ConcreteExpression leftExpr = makeConcreteValueArg(transportValueArg, factory);
      ConcreteExpression concreteTransportLam = factory.core(transportLam.computeTyped());
      List<ConcreteParameter> sigmaParams = new ArrayList<>();
      for (int i = 0; i < sigmaParamTypes.size(); i++) {
        sigmaParams.add(factory.param(true, factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(SubstitutionMeta.makeLambda(sigmaParamTypes.get(i), transportLam.getParameters().getBinding(), factory), factory.ref(jLamRef2), proj(leftExpr, i, factory))), proj(factory.ref(jPiRef), i, factory)))));
      }
      ConcreteExpression jCod = factory.appBuilder(factory.ref(ext.prelude.getEquality().getRef()))
        .app(factory.ref(typeRef), false)
        .app(factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(concreteTransportLam, factory.ref(jLamRef2), leftExpr)))
        .app(factory.ref(jPiRef))
        .build();
      ConcreteLetClause letClause = factory.letClause(typeRef, Collections.emptyList(), null, factory.app(concreteTransportLam, true, Collections.singletonList(factory.ref(jLamRef1))));
      ConcreteExpression jLam = factory.lam(Arrays.asList(factory.param(jLamRef1), factory.param(jLamRef2)), factory.letExpr(false, false, Collections.singletonList(letClause), factory.pi(Collections.singletonList(factory.param(true, Collections.singletonList(jPiRef), factory.ref(typeRef))), factory.arr(factory.sigma(sigmaParams), jCod))));

      ArendRef jArgRef = factory.local("h");
      ConcreteExpression jArg = factory.lam(Arrays.asList(factory.param(null), factory.param(jArgRef)), factory.app(factory.meta("ext", ext.extMeta), true, Collections.singletonList(factory.ref(jArgRef))));

      ConcreteExpression result = factory.app(factory.ref(ext.Jl.getRef()), true, Arrays.asList(jLam, jArg, transportPathArg, factory.core(eqRight.computeTyped()), argument));
      return letClauses.isEmpty() ? result : factory.letExpr(false, false, letClauses, result);
    }
  }

  private class SigmaProjSpec extends Spec {
    final CoreLamExpression transportLam;
    final int proj;
    final CoreClassField field;
    final CoreExpression parameterType;

    private SigmaProjSpec(CoreLamExpression transportLam, int proj, CoreClassField field, CoreExpression parameterType, ConcreteExpression concreteArg) {
      super(new ArrayList<>(), concreteArg);
      this.transportLam = transportLam;
      this.proj = proj;
      this.field = field;
      this.parameterType = parameterType;
    }

    private ConcreteExpression proj(ConcreteExpression expr, ConcreteFactory factory) {
      return field == null ? factory.proj(expr, proj) : factory.app(factory.ref(field.getRef()), false, Collections.singletonList(expr));
    }

    @Override
    public ConcreteExpression make(ConcreteFactory factory, ConcreteExpression transportLeftArg, ConcreteExpression transportRightArg, ConcreteExpression transportPathArg, CoreExpression transportValueArg, CoreExpression eqRight) {
      ArendRef jRef = factory.local("q");
      ConcreteExpression concreteValueArg = makeConcreteValueArg(transportValueArg, factory);
      ConcreteExpression jTypeLeft = proj(factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(factory.core(transportLam.computeTyped()), factory.ref(jRef), concreteValueArg)), factory);
      ConcreteExpression jTypeRight = proj(concreteValueArg, factory);
      if (parameterType.findFreeBinding(transportLam.getParameters().getBinding())) {
        ConcreteExpression rightTransportLam = SubstitutionMeta.makeLambda(parameterType, transportLam.getParameters().getBinding(), factory);
        jTypeRight = factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(rightTransportLam, factory.ref(jRef), jTypeRight));
      }
      ConcreteExpression jLam = factory.lam(Arrays.asList(factory.param(null), factory.param(jRef)), factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(jTypeLeft, jTypeRight)));
      ConcreteExpression jExpr = factory.app(factory.ref(ext.Jl.getRef()), true, Arrays.asList(jLam, factory.ref(ext.prelude.getIdp().getRef()), transportPathArg));
      ConcreteExpression result = factory.app(factory.ref(ext.concat.getRef()), true, Arrays.asList(jExpr, argument));
      return letClauses.isEmpty() ? result : factory.letExpr(false, false, letClauses, result);
    }
  }

  private Spec getSpec(CoreExpression arg, ExpressionTypechecker typechecker, ConcreteSourceNode marker, ConcreteFactory factory, List<CoreExpression> args, CoreClassField field, int proj, ConcreteExpression concreteArg) {
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
      return new EqualitySpec(lam.getParameters(), (CoreFunCallExpression) body, typechecker, marker, concreteArg);
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
        return piTree.subtrees.isEmpty() ? null : new PiSpec(piTreeMaker, piTree, letClauses, concreteArg);
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

        return new PiArgsSpec(args, lam, parameters, body, concreteArg);
      }
    }

    if (body instanceof CoreSigmaExpression || body instanceof CoreClassCallExpression) {
      CoreParameter parameters = body instanceof CoreSigmaExpression ? ((CoreSigmaExpression) body).getParameters() : ((CoreClassCallExpression) body).getClassFieldParameters();
      List<CoreClassField> classFields = body instanceof CoreClassCallExpression ? Utils.getNotImplementedField((CoreClassCallExpression) body) : null;
      if (proj == -1 && field == null) {
        List<CoreExpression> sigmaParamTypes = new ArrayList<>();
        List<Integer> indices = classFields == null ? new ArrayList<>() : null;
        Set<CoreBinding> bindings = new HashSet<>();
        int i = 0;
        for (CoreParameter param = parameters; param.hasNext(); param = param.getNext(), i++) {
          CoreExpression paramType = param.getTypeExpr();
          if (!(classFields != null && classFields.get(i).isProperty() || Utils.isProp(paramType))) {
            if (paramType.findFreeBindings(bindings) != null) {
              return null;
            }
            sigmaParamTypes.add(paramType);
            if (classFields == null) indices.add(i);
          } else if (classFields != null) {
            classFields.remove(i--);
          }
          bindings.add(param.getBinding());
        }

        if (classFields != null && concreteArg instanceof ConcreteClassExtExpression) {
          ConcreteClassExtExpression classExt = (ConcreteClassExtExpression) concreteArg;
          ConcreteExpression baseExpr = classExt.getBaseClassExpression();
          CoreDefinition def = baseExpr instanceof ConcreteReferenceExpression ? ext.definitionProvider.getCoreDefinition(((ConcreteReferenceExpression) baseExpr).getReferent()) : null;
          CoreClassDefinition classDef = ((CoreClassCallExpression) body).getDefinition();
          if (!(def instanceof CoreClassDefinition && ((CoreClassDefinition) def).isSubClassOf(classDef))) {
            typechecker.getErrorReporter().report(new SubclassError(true, classDef.getRef(), baseExpr));
            return new ErrorSpec();
          }

          Map<ArendRef, ConcreteCoclause> implMap = new HashMap<>();
          for (ConcreteCoclause coclause : classExt.getCoclauses().getCoclauseList()) {
            if (coclause.getImplementation() == null) {
              typechecker.getErrorReporter().report(new TypecheckingError("Implementation is missing", coclause));
              return new ErrorSpec();
            }

            if (implMap.putIfAbsent(coclause.getImplementedRef(), coclause) != null) {
              typechecker.getErrorReporter().report(new RedundantCoclauseError(coclause));
            }
          }

          List<ConcreteExpression> tupleFields = new ArrayList<>(classFields.size());
          List<ArendRef> notImplemented = new ArrayList<>();
          for (CoreClassField classField : classFields) {
            ConcreteCoclause coclause = implMap.remove(classField.getRef());
            if (coclause != null) {
              tupleFields.add(coclause.getImplementation());
            } else {
              notImplemented.add(classField.getRef());
            }
          }

          for (ConcreteCoclause coclause : implMap.values()) {
            typechecker.getErrorReporter().report(new RedundantCoclauseError(coclause));
          }

          if (!notImplemented.isEmpty()) {
            typechecker.getErrorReporter().report(new FieldsImplementationError(false, classDef.getRef(), notImplemented, classExt.getCoclauses()));
            return new ErrorSpec();
          }

          concreteArg = tupleFields.size() == 1 ? tupleFields.get(0) : factory.withData(classExt.getData()).tuple(tupleFields);
        }

        return new SigmaSpec(lam, sigmaParamTypes, classFields, indices, concreteArg);
      } else {
        int i = 0;
        Set<CoreBinding> bindings = new HashSet<>();
        CoreExpression parameterType = null;
        for (CoreParameter param = parameters; param.hasNext(); param = param.getNext(), i++) {
          bindings.add(param.getBinding());
          if (i == proj || classFields != null && classFields.get(i) == field) {
            CoreExpression paramType = param.getTypeExpr();
            if (paramType.findFreeBindings(bindings) != null) {
              return null;
            }
            parameterType = paramType;
            break;
          }
        }
        return parameterType == null ? null : new SigmaProjSpec(lam, proj, field, parameterType, concreteArg);
      }
    }

    CoreFunCallExpression equality = body.toEquality();
    if (equality != null ) {
      return new EqualitySpec(lam.getParameters(), equality, typechecker, marker, concreteArg);
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
      if (!(leftExpr instanceof CoreAppExpression || leftExpr instanceof CoreFieldCallExpression || leftExpr instanceof CoreProjExpression || leftExpr instanceof CoreFunCallExpression && (((CoreFunCallExpression) leftExpr).getDefinition() == ext.prelude.getCoerce() || ((CoreFunCallExpression) leftExpr).getDefinition() == ext.transport))) {
        leftExpr = leftExpr.normalize(NormalizationMode.WHNF);
      }
      if (!(leftExpr instanceof CoreAppExpression)) {
        break;
      }
      arguments.add(((CoreAppExpression) leftExpr).getArgument());
      leftExpr = ((CoreAppExpression) leftExpr).getFunction().getUnderlyingExpression();
    }
    Collections.reverse(arguments);

    CoreClassField field = null;
    int proj = -1;
    if (leftExpr instanceof CoreFieldCallExpression) {
      field = ((CoreFieldCallExpression) leftExpr).getDefinition();
      leftExpr = ((CoreFieldCallExpression) leftExpr).getArgument();
    } else if (leftExpr instanceof CoreProjExpression) {
      proj = ((CoreProjExpression) leftExpr).getField();
      leftExpr = ((CoreProjExpression) leftExpr).getExpression();
    }

    if ((field != null || proj != -1) && !(leftExpr instanceof CoreFunCallExpression && (((CoreFunCallExpression) leftExpr).getDefinition() == ext.prelude.getCoerce() || ((CoreFunCallExpression) leftExpr).getDefinition() == ext.transport))) {
      leftExpr = leftExpr.normalize(NormalizationMode.WHNF);
    }

    ConcreteExpression concreteArg = contextData.getArguments().get(0).getExpression();
    if (leftExpr instanceof CoreFunCallExpression && ((CoreFunCallExpression) leftExpr).getDefinition() == ext.transport) {
      var transportArgs = ((CoreFunCallExpression) leftExpr).getDefCallArguments();
      Spec spec = getSpec(transportArgs.get(1), typechecker, contextData.getMarker(), factory, arguments, field, proj, concreteArg);
      if (spec instanceof ErrorSpec) return null;
      if (spec != null) {
        return typechecker.typecheck(spec.make(factory, factory.core(transportArgs.get(2).computeTyped()), factory.core(transportArgs.get(3).computeTyped()), factory.core(transportArgs.get(4).computeTyped()), transportArgs.get(5), equality.getDefCallArguments().get(2)), contextData.getExpectedType());
      }
    } else {
      if (leftExpr instanceof CoreFunCallExpression && ((CoreFunCallExpression) leftExpr).getDefinition() == ext.prelude.getCoerce()) {
        var coeArgs = ((CoreFunCallExpression) leftExpr).getDefCallArguments();
        CoreExpression lastArg = coeArgs.get(2).normalize(NormalizationMode.WHNF);
        if (lastArg instanceof CoreConCallExpression && ((CoreConCallExpression) lastArg).getDefinition() == ext.prelude.getRight()) {
          Spec spec = getSpec(coeArgs.get(0), typechecker, contextData.getMarker(), factory, arguments, field, proj, concreteArg);
          if (spec instanceof ErrorSpec) return null;
          if (spec != null) {
            ArendRef iRef = factory.local("i");
            return typechecker.typecheck(spec.make(factory, factory.ref(ext.prelude.getLeft().getRef()), factory.ref(ext.prelude.getRight().getRef()), factory.app(factory.ref(ext.prelude.getPathCon().getRef()), true, Collections.singletonList(factory.lam(Collections.singletonList(factory.param(iRef)), factory.ref(iRef)))), coeArgs.get(1), equality.getDefCallArguments().get(2)), contextData.getExpectedType());
          }
        }
      }
    }

    typechecker.getErrorReporter().report(new TypeError("Type is not supported", contextData.getExpectedType(), contextData.getMarker()));
    return null;
  }
}
