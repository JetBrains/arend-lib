package org.arend.lib.meta;

import org.arend.ext.FreeBindingsModifier;
import org.arend.ext.concrete.*;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.error.*;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.error.SubclassError;
import org.arend.lib.error.TypeError;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class ExtMeta extends BaseMetaDefinition implements MetaResolver {
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

  @Override
  public boolean allowCoclauses() {
    return true;
  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    if (!checkArguments(contextData.getArguments(), resolver.getErrorReporter(), contextData.getMarker(), argumentExplicitness())) {
      return null;
    }

    ConcreteCoclauses coclauses = contextData.getCoclauses();
    if (coclauses != null && contextData.getArguments().isEmpty()) {
      resolver.getErrorReporter().report(new NameResolverError("Expected a class name", coclauses));
      return null;
    }

    if (contextData.getArguments().isEmpty()) {
      return contextData.getReferenceExpression();
    }

    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());
    ConcreteExpression arg = contextData.getArguments().get(0).getExpression();
    return factory.app(contextData.getReferenceExpression(), true, Collections.singletonList(resolver.resolve(coclauses == null ? arg : factory.classExt(arg, coclauses.getCoclauseList()))));
  }

  private static class PiTree {
    public final CoreParameter parameter;
    public final ConcreteExpression head;
    public final ConcreteExpression altHead;
    public final List<Integer> indices;
    public final List<PiTree> subtrees;
    public final boolean isNonDependent;

    private PiTree(CoreParameter parameter, ConcreteExpression head, ConcreteExpression altHead, List<Integer> indices, List<PiTree> subtrees) {
      this.parameter = parameter;
      this.head = head;
      this.altHead = altHead;
      this.indices = indices;
      this.subtrees = subtrees;

      boolean nonDependent = indices.isEmpty();
      if (nonDependent) {
        for (PiTree subtree : subtrees) {
          if (!subtree.isNonDependent) {
            nonDependent = false;
            break;
          }
        }
      }
      isNonDependent = nonDependent;
    }
  }

  private class PiTreeMaker {
    private final ExpressionTypechecker typechecker;
    private final ConcreteFactory factory;
    private final List<ConcreteLetClause> clauses;
    private List<ConcreteParameter> lamParams;
    private List<SubstitutionPair> substitution;
    private int index = 1;

    private PiTreeMaker(ExpressionTypechecker typechecker, ConcreteFactory factory, List<ConcreteLetClause> clauses) {
      this.typechecker = typechecker;
      this.factory = factory;
      this.clauses = clauses;
    }

    private PiTree make(CoreParameter parameter, CoreExpression expr) {
      List<CoreParameter> params = new ArrayList<>();
      CoreExpression codomain = expr.getPiParameters(params);
      Set<? extends CoreBinding> freeVars = codomain.findFreeBindings();

      boolean found = false;
      for (CoreParameter param : params) {
        if (freeVars.remove(param.getBinding())) {
          found = true;
        }
      }
      if (found) {
        params.clear();
        codomain = expr;
      }

      ConcreteExpression concrete;
      List<Integer> indices;
      if (freeVars.isEmpty()) {
        concrete = factory.core(codomain.computeTyped());
        indices = Collections.emptyList();
      } else {
        indices = new ArrayList<>(freeVars.size());
        for (int i = 0; i < substitution.size(); i++) {
          if (freeVars.contains(substitution.get(i).binding)) {
            indices.add(i);
          }
        }

        List<ConcreteParameter> redLamParams;
        List<SubstitutionPair> redSubstitution;
        if (indices.size() == substitution.size()) {
          redLamParams = lamParams;
          redSubstitution = substitution;
        } else {
          redLamParams = new ArrayList<>(indices.size());
          redSubstitution = new ArrayList<>(indices.size());
          for (Integer index : indices) {
            redLamParams.add(lamParams.get(index));
            redSubstitution.add(substitution.get(index));
          }
        }

        CoreExpression finalCodomain = codomain;
        TypedExpression result = typechecker.typecheck(factory.lam(redLamParams, factory.meta("ext_sigma_pi_param", new MetaDefinition() {
          @Override
          public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
            CoreExpression result = typechecker.substitute(finalCodomain, null, redSubstitution);
            return result == null ? null : result.computeTyped();
          }
        })), null);
        if (result == null) return null;
        concrete = factory.core(result);
      }

      ConcreteExpression altHead;
      if (concrete instanceof ConcreteReferenceExpression) {
        altHead = concrete;
      } else {
        ArendRef letRef = factory.local("T" + index++);
        clauses.add(factory.letClause(letRef, Collections.emptyList(), null, concrete));
        altHead = factory.ref(letRef);
      }

      List<PiTree> subtrees = new ArrayList<>(params.size());
      for (CoreParameter param : params) {
        PiTree subtree = make(param, param.getTypeExpr());
        if (subtree == null) return null;
        subtrees.add(subtree);
      }
      return new PiTree(parameter, concrete, altHead, indices, subtrees);
    }

    private PiTree make(CoreParameter param, CoreExpression expr, List<CoreParameter> parameters) {
      lamParams = new ArrayList<>(parameters.size());
      substitution = new ArrayList<>(parameters.size());
      for (int i = 0; i < parameters.size(); i++) {
        CoreParameter parameter = parameters.get(i);
        ArendRef ref = factory.local("x" + (i + 1));
        lamParams.add(factory.param(true, Collections.singletonList(ref), factory.core(parameter.getTypedType())));
        substitution.add(new SubstitutionPair(parameter.getBinding(), factory.ref(ref)));
      }
      return make(param, expr);
    }


    private ConcreteExpression makeConcrete(PiTree tree, boolean useLet, List<ConcreteExpression> args) {
      return makeConcrete(tree, useLet, args, args, true);
    }

    private ConcreteExpression makeConcrete(PiTree tree, boolean useLet, List<ConcreteExpression> evenArgs, List<ConcreteExpression> oddArgs, boolean isEven) {
      ConcreteExpression result = useLet ? tree.altHead : tree.head;
      if (!tree.indices.isEmpty()) {
        List<ConcreteExpression> headArgs = new ArrayList<>(tree.indices.size());
        for (Integer index : tree.indices) {
          headArgs.add((isEven ? evenArgs : oddArgs).get(index));
        }
        result = factory.app(useLet ? tree.altHead : tree.head, true, headArgs);
      }

      for (int i = tree.subtrees.size() - 1; i >= 0; i--) {
        result = factory.arr(makeConcrete(tree.subtrees.get(i), useLet, evenArgs, oddArgs, !isEven), result);
      }
      return result;
    }

    private ConcreteExpression makeCoe(PiTree tree, boolean useHead, boolean useLet, List<ConcreteExpression> pathRefs, ConcreteExpression arg) {
      ArendRef coeRef = factory.local("i");
      ConcreteExpression coeLam = factory.lam(Collections.singletonList(factory.param(coeRef)), factory.meta("ext_coe", new MetaDefinition() {
        @Override
        public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          List<ConcreteExpression> args = new ArrayList<>();
          for (ConcreteExpression pathRef : pathRefs) {
            args.add(factory.app(factory.ref(ext.prelude.getAt().getRef()), true, Arrays.asList(pathRef, factory.ref(coeRef))));
          }
          return typechecker.typecheck(useHead ? factory.app(useLet ? tree.altHead : tree.head, true, args) : makeConcrete(tree, useLet, args), null);
        }
      }));
      return factory.app(factory.ref(ext.prelude.getCoerce().getRef()), true, Arrays.asList(coeLam, arg, factory.ref(ext.prelude.getRight().getRef())));
    }

    private ConcreteExpression etaExpand(PiTree tree, ConcreteExpression fun, List<ConcreteArgument> args, boolean insertCoe, boolean useLet, List<ConcreteExpression> pathRefs) {
      List<ConcreteArgument> expandedArgs = new ArrayList<>(args.size());
      for (int i = 0; i < args.size(); i++) {
        PiTree subtree = tree.subtrees.get(i);
        List<ConcreteParameter> lamParams = new ArrayList<>(subtree.subtrees.size());
        List<ConcreteArgument> lamRefs = new ArrayList<>(subtree.subtrees.size());
        for (int j = 0; j < subtree.subtrees.size(); j++) {
          ArendRef lamRef = factory.local("x" + index++);
          boolean isExplicit = subtree.subtrees.get(j).parameter.isExplicit();
          lamParams.add(factory.param(isExplicit, lamRef));
          lamRefs.add(factory.arg(factory.ref(lamRef), isExplicit));
        }
        expandedArgs.add(factory.arg(factory.lam(lamParams, etaExpand(subtree, args.get(i).getExpression(), lamRefs, !insertCoe, useLet, pathRefs)), args.get(i).isExplicit()));
      }

      ConcreteExpression result = factory.app(fun, expandedArgs);
      if (!insertCoe || tree.indices.isEmpty()) {
        return result;
      }

      if (tree.indices.size() == 1) {
        return factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(useLet ? tree.altHead : tree.head, pathRefs.get(tree.indices.get(0)), result));
      }

      return makeCoe(tree, true, useLet, pathRefs, result);
    }

    private ConcreteExpression makeArgType(PiTree tree, boolean useLet, List<ConcreteExpression> leftRefs, List<ConcreteExpression> rightRefs, List<ConcreteExpression> pathRefs, ConcreteExpression leftFun, ConcreteExpression rightFun) {
      List<ConcreteArgument> piRefs = new ArrayList<>(tree.subtrees.size());
      List<ConcreteParameter> piParams = new ArrayList<>(tree.subtrees.size());
      for (int i = 0; i < tree.subtrees.size(); i++) {
        ArendRef piRef = factory.local(ext.renamerFactory.getNameFromBinding(tree.subtrees.get(i).parameter.getBinding(), "s"));
        piRefs.add(factory.arg(factory.ref(piRef), tree.subtrees.get(i).parameter.isExplicit()));
        piParams.add(factory.param(true, Collections.singletonList(piRef), makeConcrete(tree.subtrees.get(i), useLet, leftRefs, rightRefs, true)));
      }

      index = 1;
      ConcreteExpression leftArg = etaExpand(tree, leftFun, piRefs, true, useLet, pathRefs);
      index = 1;
      ConcreteExpression rightArg = etaExpand(tree, rightFun, piRefs, false, useLet, pathRefs);
      return factory.pi(piParams, factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(leftArg, rightArg)));
    }
  }

  private static class PiTreeData {
    private final PiTreeMaker maker;
    private final PiTree tree;
    private final List<ConcreteExpression> leftProjs;

    private PiTreeData(PiTreeMaker maker, PiTree tree, List<ConcreteExpression> leftProjs) {
      this.maker = maker;
      this.tree = tree;
      this.leftProjs = leftProjs;
    }
  }

  private static boolean useLet(CoreExpression expr, int index) {
    if (expr instanceof CoreReferenceExpression) {
      return false;
    }
    if (!(expr instanceof CoreTupleExpression)) {
      return true;
    }
    CoreTupleExpression tuple = (CoreTupleExpression) expr;
    return !(index < tuple.getFields().size() && tuple.getFields().get(index) instanceof CoreReferenceExpression);
  }

  private static ConcreteExpression makeProj(ConcreteFactory factory, ConcreteExpression expr, int index, List<CoreClassField> fields) {
    return fields == null ? factory.proj(expr, index) : factory.app(factory.ref(fields.get(index).getRef()), false, Collections.singletonList(expr));
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

    private ConcreteExpression applyAt(ConcreteExpression arg, ArendRef iRef) {
      return factory.app(factory.ref(ext.prelude.getAt().getRef()), true, Arrays.asList(arg, factory.ref(iRef)));
    }

    private ConcreteExpression applyAt(ConcreteExpression arg) {
      return applyAt(arg, iRef);
    }

    private TypedExpression hidingIRef(ConcreteExpression expr, CoreExpression type) {
      return typechecker.withFreeBindings(new FreeBindingsModifier().remove(typechecker.getFreeBinding(iRef)), tc -> tc.typecheck(expr, type));
    }

    private ConcreteExpression makeCoeLambda(CoreParameter typeParams, CoreBinding paramBinding, Set<CoreBinding> used, Map<CoreBinding, ConcreteExpression> sigmaRefs, ConcreteFactory factory) {
      ArendRef coeRef = factory.local("i");
      return factory.lam(Collections.singletonList(factory.param(coeRef)), factory.meta("ext_coe", new MetaDefinition() {
        @Override
        public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          List<SubstitutionPair> substitution = new ArrayList<>();
          for (CoreParameter param = typeParams; param.getBinding() != paramBinding; param = param.getNext()) {
            if (used == null || used.contains(param.getBinding())) {
              substitution.add(new SubstitutionPair(param.getBinding(), factory.app(factory.ref(ext.prelude.getAt().getRef()), true, Arrays.asList(sigmaRefs.get(param.getBinding()), factory.ref(coeRef)))));
            }
          }
          CoreExpression result = typechecker.substitute(paramBinding.getTypeExpr(), null, substitution);
          return result == null ? null : result.computeTyped();
        }
      }));
    }

    private ConcreteExpression generate(ConcreteExpression arg, CoreExpression type, CoreExpression coreLeft, CoreExpression coreRight) {
      ConcreteExpression left = factory.core(coreLeft.computeTyped());
      ConcreteExpression right = factory.core(coreRight.computeTyped());

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

      if (type instanceof CoreSigmaExpression || type instanceof CoreClassCallExpression) {
        CoreParameter typeParams = type instanceof CoreSigmaExpression ? ((CoreSigmaExpression) type).getParameters() : ((CoreClassCallExpression) type).getClassFieldParameters();
        List<CoreClassField> classFields;
        if (type instanceof CoreSigmaExpression) {
          classFields = null;
        } else {
          classFields = new ArrayList<>();
          CoreClassCallExpression classCall = (CoreClassCallExpression) type;
          for (CoreClassField field : classCall.getDefinition().getFields()) {
            if (!classCall.isImplemented(field)) {
              classFields.add(field);
            }
          }
        }

        Set<CoreBinding> bindings = new HashSet<>();
        Set<CoreBinding> dependentBindings = new HashSet<>();
        List<ConcreteParameter> sigmaParams = new ArrayList<>();
        Map<CoreBinding, ConcreteExpression> sigmaRefs = new HashMap<>();
        ConcreteExpression lastSigmaParam = null;
        Set<CoreBinding> propBindings = new HashSet<>();
        Set<CoreClassField> propFields = new HashSet<>();
        Set<CoreBinding> totalUsed = new HashSet<>();
        List<Set<CoreBinding>> usedList = new ArrayList<>();
        List<ConcreteLetClause> letClauses = new ArrayList<>();
        List<PiTreeData> piTreeDataList = new ArrayList<>();
        int i = 0;
        for (CoreParameter param = typeParams; param.hasNext(); param = param.getNext(), i++) {
          Set<CoreBinding> used = new HashSet<>();
          CoreBinding paramBinding = param.getBinding();
          boolean isProp = classFields != null && classFields.get(i).isProperty() || isProp(paramBinding.getTypeExpr());
          if (isProp) {
            propBindings.add(paramBinding);
            if (classFields != null) {
              propFields.add(classFields.get(i));
            }
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
              typechecker.getErrorReporter().report(new TypecheckingError((type instanceof CoreSigmaExpression ? "\\Sigma types" : "Classes") + " with more than two levels of dependencies are not supported", marker));
              return null;
            }
          }
          bindings.add(paramBinding);
          totalUsed.addAll(used);
          usedList.add(used);

          ArendRef sigmaRef = factory.local("p" + (i + 1));
          PiTreeData piTreeData = null;
          if (!isProp) {
            boolean isPi = false;
            ConcreteExpression leftExpr = makeProj(factory, left, i, classFields);
            CoreExpression paramType = param.getTypeExpr().normalize(NormalizationMode.WHNF);
            if (paramType instanceof CorePiExpression) {
              List<CoreParameter> sigmaParameters = new ArrayList<>();
              List<ConcreteExpression> leftProjs = new ArrayList<>();
              List<ConcreteExpression> rightProjs = new ArrayList<>();
              List<ConcreteExpression> pathRefs = new ArrayList<>();
              int j = 0;
              for (CoreParameter parameter = typeParams; parameter != param; parameter = parameter.getNext(), j++) {
                if (used.contains(parameter.getBinding())) {
                  sigmaParameters.add(parameter);
                  leftProjs.add(makeProj(factory, left, j, classFields));
                  rightProjs.add(makeProj(factory, right, j, classFields));
                  pathRefs.add(sigmaRefs.get(parameter.getBinding()));
                }
              }

              PiTreeMaker piTreeMaker = new PiTreeMaker(typechecker, factory, letClauses);
              PiTree piTree = piTreeMaker.make(param, paramType, sigmaParameters);
              if (piTree == null) return null;
              if (!piTree.subtrees.isEmpty()) {
                piTreeData = new PiTreeData(piTreeMaker, piTree, leftProjs);
                lastSigmaParam = piTreeMaker.makeArgType(piTreeData.tree, false, leftProjs, rightProjs, pathRefs, makeProj(factory, left, j, classFields), makeProj(factory, right, j, classFields));
                isPi = true;
              }
            }

            if (!isPi && dependentBindings.contains(paramBinding)) {
              if (used.size() > 1) {
                leftExpr = factory.app(factory.ref(ext.prelude.getCoerce().getRef()), true, Arrays.asList(makeCoeLambda(typeParams, paramBinding, used, sigmaRefs, factory), leftExpr, factory.ref(ext.prelude.getRight().getRef())));
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

            if (!isPi) {
              lastSigmaParam = factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(leftExpr, makeProj(factory, right, i, classFields)));
            }
            sigmaParams.add(factory.param(true, Collections.singletonList(sigmaRef), lastSigmaParam));
          }

          ConcreteExpression sigmaRefExpr = factory.ref(sigmaRef);
          if (piTreeData != null && piTreeData.tree.isNonDependent) {
            PiTree piTree = piTreeData.tree;
            List<ConcreteParameter> lamParams = new ArrayList<>(piTree.subtrees.size() + 1);
            List<ConcreteArgument> args = new ArrayList<>(piTree.subtrees.size());
            ArendRef iRef = factory.local("i");
            lamParams.add(factory.param(iRef));
            for (PiTree subtree : piTree.subtrees) {
              ArendRef ref = factory.local(ext.renamerFactory.getNameFromBinding(subtree.parameter.getBinding(), null));
              lamParams.add(factory.param(subtree.parameter.isExplicit(), ref));
              args.add(factory.arg(factory.ref(ref), subtree.parameter.isExplicit()));
            }
            sigmaRefExpr = factory.app(factory.ref(ext.prelude.getPathCon().getRef()), true, Collections.singletonList(factory.lam(lamParams, applyAt(factory.app(sigmaRefExpr, args), iRef))));
          }

          sigmaRefs.put(paramBinding, sigmaRefExpr);
          piTreeDataList.add(piTreeData);
        }

        TypedExpression sigmaEqType = typechecker.typecheck(sigmaParams.size() == 1 ? lastSigmaParam : factory.sigma(sigmaParams), null);
        if (sigmaEqType == null) return null;
        if (!(type instanceof CoreSigmaExpression)) {
          CoreClassCallExpression classCall = (CoreClassCallExpression) type;
          ConcreteExpression baseExpr = arg instanceof ConcreteClassExtExpression ? ((ConcreteClassExtExpression) arg).getBaseClassExpression() : arg;
          CoreDefinition def = ext.definitionProvider.getCoreDefinition(baseExpr instanceof ConcreteReferenceExpression ? ((ConcreteReferenceExpression) baseExpr).getReferent() : null);
          boolean isSubclass = def instanceof CoreClassDefinition && ((CoreClassDefinition) def).isSubClassOf(classCall.getDefinition());
          if (arg instanceof ConcreteClassExtExpression && !isSubclass) {
            typechecker.getErrorReporter().report(new SubclassError(classCall.getDefinition().getRef(), baseExpr));
            return null;
          }

          if (isSubclass) {
            Map<ArendRef, ConcreteCoclause> implMap = new HashMap<>();
            if (arg instanceof ConcreteClassExtExpression) {
              for (ConcreteCoclause coclause : ((ConcreteClassExtExpression) arg).getCoclauses().getCoclauseList()) {
                if (implMap.putIfAbsent(coclause.getImplementedRef(), coclause) != null) {
                  typechecker.getErrorReporter().report(new RedundantCoclauseError(coclause));
                }
              }
            }

            List<ConcreteExpression> tupleFields = new ArrayList<>(classFields.size());
            List<ArendRef> notImplemented = new ArrayList<>();
            for (CoreClassField field : classFields) {
              if (!propFields.contains(field)) {
                ConcreteCoclause coclause = implMap.remove(field.getRef());
                if (coclause != null) {
                  tupleFields.add(coclause.getImplementation());
                } else {
                  notImplemented.add(field.getRef());
                }
              }
            }

            for (ConcreteCoclause coclause : implMap.values()) {
              typechecker.getErrorReporter().report(new RedundantCoclauseError(coclause));
            }

            if (!notImplemented.isEmpty()) {
              typechecker.getErrorReporter().report(new FieldsImplementationError(false, classCall.getDefinition().getRef(), notImplemented, arg instanceof ConcreteClassExtExpression ? ((ConcreteClassExtExpression) arg).getCoclauses() : marker));
              return null;
            }

            arg = tupleFields.size() == 1 ? tupleFields.get(0) : factory.withData(arg.getData()).tuple(tupleFields);
          }
        }
        TypedExpression result = hidingIRef(arg, sigmaEqType.getExpression());
        if (result == null) return null;

        ArendRef letRef;
        ConcreteExpression concreteTuple;
        CoreExpression resultExpr = result.getExpression().getUnderlyingExpression();
        if (resultExpr instanceof CoreReferenceExpression) {
          letRef = null;
          concreteTuple = factory.core(result);
        } else {
          letRef = factory.local("arg");
          concreteTuple = factory.ref(letRef);
        }

        if (letRef != null) {
          letClauses.add(factory.letClause(letRef, Collections.emptyList(), null, factory.core(result)));
        }

        List<ConcreteExpression> fields = new ArrayList<>();
        Map<CoreBinding, ConcreteExpression> fieldsMap = new HashMap<>();
        i = 0;
        for (CoreParameter param = typeParams; param.hasNext(); param = param.getNext(), i++) {
          ConcreteExpression field;
          ConcreteExpression fieldWithAt = null;
          CoreBinding paramBinding = param.getBinding();
          boolean useLet;
          if (propBindings.contains(paramBinding)) {
            field = factory.app(factory.ref(ext.pathInProp.getRef()), true, Arrays.asList(makeCoeLambda(typeParams, paramBinding, usedList.get(i), fieldsMap, factory), makeProj(factory, left, i, classFields), makeProj(factory, right, i, classFields)));
            useLet = true;
          } else {
            boolean isDependent = dependentBindings.contains(paramBinding);
            if (isDependent) {
              useLet = true;
            } else {
              if (sigmaParams.size() == 1) {
                useLet = false;
              } else {
                useLet = useLet(resultExpr, i);
              }
            }

            ConcreteExpression proj = sigmaParams.size() == 1 ? concreteTuple : factory.proj(concreteTuple, i);
            if (piTreeDataList.get(i) != null) {
              PiTreeMaker piTreeMaker = piTreeDataList.get(i).maker;
              PiTree piTree = piTreeDataList.get(i).tree;
              if (piTree.isNonDependent) {
                useLet = true;
                List<ConcreteParameter> lamParams = new ArrayList<>(piTree.subtrees.size() + 1);
                List<ConcreteArgument> args = new ArrayList<>(piTree.subtrees.size());
                ArendRef iRef = factory.local("i");
                lamParams.add(factory.param(iRef));
                for (PiTree subtree : piTree.subtrees) {
                  ArendRef ref = factory.local(ext.renamerFactory.getNameFromBinding(subtree.parameter.getBinding(), null));
                  lamParams.add(factory.param(subtree.parameter.isExplicit(), ref));
                  args.add(factory.arg(factory.ref(ref), subtree.parameter.isExplicit()));
                }
                fieldWithAt = factory.lam(lamParams.subList(1, lamParams.size()), applyAt(factory.app(proj, args), this.iRef));
                proj = factory.app(factory.ref(ext.prelude.getPathCon().getRef()), true, Collections.singletonList(factory.lam(lamParams, applyAt(factory.app(proj, args), iRef))));
              } else {
                if (!(coreLeft instanceof CoreReferenceExpression)) {
                  ArendRef projRef = factory.local("l");
                  letClauses.add(factory.letClause(projRef, Collections.emptyList(), null, left));
                  left = factory.ref(projRef);
                }

                List<ConcreteExpression> rightRefs = new ArrayList<>();
                List<ConcreteExpression> pathRefs = new ArrayList<>();
                List<ConcreteCaseArgument> caseArgs = new ArrayList<>();
                List<ConcretePattern> casePatterns = new ArrayList<>();
                ArendRef lastCaseRef = factory.local("a");
                int j = 0, k = 0;
                for (CoreParameter parameter = typeParams; parameter != param; parameter = parameter.getNext(), j++) {
                  if (usedList.get(i).contains(parameter.getBinding())) {
                    ArendRef rightRef = factory.local("r" + (j + 1));
                    rightRefs.add(factory.ref(rightRef));
                    caseArgs.add(factory.caseArg(makeProj(factory, right, j, classFields), rightRef, null));

                    ArendRef pathRef = factory.local("q" + (k + 1));
                    pathRefs.add(factory.ref(pathRef));
                    caseArgs.add(factory.caseArg(factory.proj(concreteTuple, k), pathRef, factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(makeProj(factory, left, j, classFields), factory.ref(rightRef)))));

                    casePatterns.add(factory.refPattern(null, null));
                    casePatterns.add(factory.conPattern(ext.prelude.getIdp().getRef()));
                  }

                  if (!propBindings.contains(parameter.getBinding())) {
                    k++;
                  }
                }

                ArendRef rightFunRef = factory.local("f");
                caseArgs.add(factory.caseArg(makeProj(factory, right, j, classFields), rightFunRef, piTreeMaker.makeConcrete(piTree, true, rightRefs)));
                caseArgs.add(factory.caseArg(factory.proj(concreteTuple, k), null, piTreeMaker.makeArgType(piTree, true, piTreeDataList.get(i).leftProjs, rightRefs, pathRefs, makeProj(factory, left, j, classFields), factory.ref(rightFunRef))));

                casePatterns.add(factory.refPattern(null, null));
                casePatterns.add(factory.refPattern(lastCaseRef, null));

                ConcreteExpression caseResultType = factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(piTreeMaker.makeCoe(piTree, false, true, pathRefs, makeProj(factory, left, j, classFields)), factory.ref(rightFunRef)));
                proj = factory.caseExpr(false, caseArgs, caseResultType, null, factory.clause(casePatterns, factory.app(factory.meta("ext", ExtMeta.this), true, Collections.singletonList(factory.ref(lastCaseRef)))));
              }
            }

            field = isDependent ? factory.appBuilder(factory.ref(ext.pathOver.getRef())).app(makeCoeLambda(typeParams, paramBinding, usedList.get(i), fieldsMap, factory), false).app(proj).build() : proj;
          }

          if (useLet && totalUsed.contains(paramBinding)) {
            ArendRef argLetRef = factory.local("h" + (i + 1));
            letClauses.add(factory.letClause(argLetRef, Collections.emptyList(), null, field));
            field = factory.ref(argLetRef);
          }
          fields.add(fieldWithAt == null ? applyAt(field) : fieldWithAt);
          fieldsMap.put(paramBinding, field);
        }

        ConcreteExpression concreteResult;
        if (type instanceof CoreClassCallExpression) {
          List<ConcreteClassElement> classElements = new ArrayList<>(classFields.size());
          for (int j = 0; j < classFields.size(); j++) {
            classElements.add(factory.implementation(classFields.get(j).getRef(), fields.get(j)));
          }
          concreteResult = factory.newExpr(factory.classExt(factory.ref(((CoreClassCallExpression) type).getDefinition().getRef()), classElements));
        } else {
          concreteResult = factory.tuple(fields);
        }
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

    CoreExpression normType = type.normalize(NormalizationMode.WHNF);
    ConcreteExpression arg = args.get(0).getExpression();
    if (normType instanceof CoreUniverseExpression) {
      ConcreteExpression left = factory.core(equality.getDefCallArguments().get(1).computeTyped());
      ConcreteExpression right = factory.core(equality.getDefCallArguments().get(2).computeTyped());
      if (((CoreUniverseExpression) normType).getSort().isProp()) {
        TypedExpression expectedType = typechecker.typecheck(factory.sigma(Arrays.asList(factory.param(true, factory.arr(left, right)), factory.param(true, factory.arr(right, left)))), null);
        if (expectedType == null) return null;
        TypedExpression typedArg = typechecker.typecheck(arg, expectedType.getExpression());
        if (typedArg == null) return null;
        CoreExpression coreArg = typedArg.getExpression().getUnderlyingExpression();
        ConcreteExpression concreteArg = factory.core(typedArg);
        ArendRef letRef;
        ConcreteExpression concreteResult;
        if (coreArg instanceof CoreReferenceExpression || coreArg instanceof CoreTupleExpression) {
          letRef = null;
          concreteResult = concreteArg;
        } else {
          letRef = factory.local("h");
          concreteResult = factory.ref(letRef);
        }
        ConcreteExpression result = factory.app(factory.ref(ext.propExt.getRef()), true, Arrays.asList(factory.proj(concreteResult, 0), factory.proj(concreteResult, 1)));
        return typechecker.typecheck(letRef == null ? result : factory.letExpr(false, Collections.singletonList(factory.letClause(letRef, Collections.emptyList(), null, concreteArg)), result), contextData.getExpectedType());
      } else {
        TypedExpression expectedType = typechecker.typecheck(factory.app(factory.ref(ext.equationMeta.Equiv.getRef()), false, Arrays.asList(left, right)), null);
        if (expectedType == null) return null;
        TypedExpression typedArg = typechecker.typecheck(arg, expectedType.getExpression());
        if (typedArg == null) return null;
        CoreExpression actualType = typedArg.getType().normalize(NormalizationMode.WHNF);
        return typechecker.typecheck(factory.app(factory.ref(actualType instanceof CoreClassCallExpression && ((CoreClassCallExpression) actualType).getDefinition().isSubClassOf(ext.equationMeta.QEquiv) ? ext.equationMeta.qEquivToEq.getRef() : ext.equationMeta.equivToEq.getRef()), true, Collections.singletonList(factory.core(typedArg))), contextData.getExpectedType());
      }
    }

    ArendRef iRef = factory.local("i");
    return typechecker.typecheck(factory.app(factory.ref(ext.prelude.getPathCon().getRef()), true, Collections.singletonList(factory.lam(Collections.singletonList(factory.param(iRef)), factory.meta("ext_result", new MetaDefinition() {
      @Override
      public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        ConcreteExpression result = new ExtGenerator(typechecker, factory, marker, iRef).generate(arg, normType, equality.getDefCallArguments().get(1), equality.getDefCallArguments().get(2));
        return result == null ? null : typechecker.typecheck(result, normType);
      }
    })))), contextData.getExpectedType());
  }
}
