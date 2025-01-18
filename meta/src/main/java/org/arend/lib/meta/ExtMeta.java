package org.arend.lib.meta;

import org.arend.ext.FreeBindingsModifier;
import org.arend.ext.concrete.*;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.level.CoreLevel;
import org.arend.ext.core.level.LevelSubstitution;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.error.*;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.ext.ui.ArendUI;
import org.arend.lib.StdExtension;
import org.arend.lib.error.IgnoredArgumentError;
import org.arend.lib.error.SubclassError;
import org.arend.lib.error.TypeError;
import org.arend.lib.meta.pi_tree.*;
import org.arend.lib.meta.util.SubstitutionMeta;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Consumer;

public class ExtMeta extends BaseMetaDefinition {
  private final StdExtension ext;
  private final boolean withSimpCoe;

  public ExtMeta(StdExtension ext, boolean withSimpCoe) {
    this.ext = ext;
    this.withSimpCoe = withSimpCoe;
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

  private static class PiTreeData {
    private final PiTreeMaker maker;
    private final PiTreeRoot tree;
    private final List<ConcreteExpression> leftProjs;

    private PiTreeData(PiTreeMaker maker, PiTreeRoot tree, List<ConcreteExpression> leftProjs) {
      this.maker = maker;
      this.tree = tree;
      this.leftProjs = leftProjs;
    }
  }

  private static boolean useLet(CoreExpression expr, int index) {
    return !(expr instanceof CoreReferenceExpression) && (!(expr instanceof CoreTupleExpression tuple) || !(index < tuple.getFields().size() && tuple.getFields().get(index) instanceof CoreReferenceExpression));
  }

  private static ConcreteExpression makeProj(ConcreteFactory factory, ConcreteExpression expr, int index, List<CoreClassField> fields) {
    return fields == null ? factory.proj(expr, index) : factory.app(factory.ref(fields.get(index).getRef()), false, Collections.singletonList(expr));
  }

  private static class CoclauseData {
    final ConcreteCoclause coclause;
    final boolean fromField;

    private CoclauseData(ConcreteCoclause coclause, boolean fromField) {
      this.coclause = coclause;
      this.fromField = fromField;
    }
  }

  private static class FieldPathExpression extends PathExpression {
    final CoreClassField classField;

    FieldPathExpression(CoreClassField classField, ConcreteExpression pathExpression) {
      super(pathExpression);
      this.classField = classField;
    }

    @Override
    public ConcreteExpression applyAt(ArendRef iRef, ConcreteFactory factory, StdExtension ext) {
      return factory.app(factory.ref(classField.getRef()), false, Collections.singletonList(applyAt(pathExpression, iRef, factory, ext)));
    }
  }

  private static ConcreteExpression addImplicitLambda(ConcreteExpression expr, CoreExpression type, ConcreteFactory factory) {
    type = type.normalize(NormalizationMode.WHNF);
    if (type instanceof CorePiExpression && !((CorePiExpression) type).getParameters().isExplicit()) {
      String name = ((CorePiExpression) type).getParameters().getBinding().getName();
      ArendRef ref = factory.local(name != null ? name : "x");
      return factory.lam(Collections.singletonList(factory.param(false, ref)), factory.app(expr, false, factory.ref(ref)));
    } else {
      return expr;
    }
  }

  public class ExtGenerator {
    private final ExpressionTypechecker typechecker;
    private final ConcreteFactory factory;
    private final ConcreteSourceNode marker;
    private final ArendRef iRef;
    private CoreErrorExpression goalExpr;

    private ExtGenerator(ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteSourceNode marker, ArendRef iRef) {
      this.typechecker = typechecker;
      this.factory = factory;
      this.marker = marker;
      this.iRef = iRef;
    }

    private ConcreteExpression applyAt(ConcreteExpression arg, ArendRef iRef) {
      return factory.app(factory.ref(ext.prelude.getAtRef()), true, Arrays.asList(arg, factory.ref(iRef)));
    }

    private ConcreteExpression applyAt(ConcreteExpression arg) {
      return applyAt(arg, iRef);
    }

    private ConcreteExpression applyPath(ArendRef iRef, ConcreteExpression expr) {
      return factory.app(factory.ref(ext.prelude.getPathConRef()), true, Collections.singletonList(factory.lam(Collections.singletonList(factory.param(iRef)), expr)));
    }

    private TypedExpression checkGoals(TypedExpression typed) {
      if (typed == null || goalExpr != null) return typed;
      typed.getExpression().processSubexpression(expr -> {
        if (expr instanceof CoreErrorExpression && ((CoreErrorExpression) expr).isGoal() && goalExpr == null) {
          goalExpr = (CoreErrorExpression) expr;
          return CoreExpression.FindAction.STOP;
        }
        return CoreExpression.FindAction.CONTINUE;
      });
      return typed;
    }

    private TypedExpression hidingIRef(ConcreteExpression expr, CoreExpression type) {
      CoreBinding binding = typechecker.getFreeBinding(iRef);
      return binding == null ? typechecker.typecheck(expr, type) : checkGoals(typechecker.withFreeBindings(new FreeBindingsModifier().remove(binding), tc -> tc.typecheck(expr, type)));
    }

    private ConcreteExpression makeCoeLambda(CoreParameter typeParams, CoreBinding paramBinding, CoreExpression paramType, Set<CoreBinding> used, Map<CoreBinding, PathExpression> sigmaRefs, ConcreteFactory factory) {
      ArendRef coeRef = factory.local("i");
      return factory.lam(Collections.singletonList(factory.param(coeRef)), factory.meta("ext_coe", new MetaDefinition() {
        @Override
        public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
          List<SubstitutionPair> substitution = new ArrayList<>();
          for (CoreParameter param = typeParams; param.getBinding() != paramBinding; param = param.getNext()) {
            if (used == null || used.contains(param.getBinding())) {
              substitution.add(new SubstitutionPair(param.getBinding(), sigmaRefs.get(param.getBinding()).applyAt(coeRef, factory, ext)));
            }
          }
          CoreExpression result = typechecker.substitute((paramType == null ? paramBinding.getTypeExpr() : paramType).normalize(NormalizationMode.WHNF), LevelSubstitution.EMPTY, substitution);
          return result == null ? null : result.computeTyped(true);
        }
      }));
    }

    private ConcreteExpression generate(ConcreteExpression arg, CoreExpression type, CoreExpression coreLeft, CoreExpression coreRight) {
      TypedExpression leftTyped = coreLeft.computeTyped();
      TypedExpression rightTyped = coreRight.computeTyped();
      ConcreteExpression left = factory.core(leftTyped);
      ConcreteExpression right = factory.core(rightTyped);

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
          concretePiParams.add(factory.param(piParam.isExplicit(), Collections.singletonList(ref), factory.meta("ext_param", new SubstitutionMeta(piParam.getTypeExpr(), substitution.subList(0, i)))));
          concreteLamParams.add(factory.param(piParam.isExplicit(), ref));
          ConcreteExpression refExpr = factory.ref(ref);
          args.add(factory.arg(refExpr, piParam.isExplicit()));
          substitution.add(new SubstitutionPair(piParam.getBinding(), refExpr));
        }

        TypedExpression piEqType = typechecker.typecheck(factory.pi(concretePiParams, factory.app(factory.ref(ext.prelude.getEqualityRef()), true, Arrays.asList(factory.app(left, args), factory.app(right, args)))), null);
        if (piEqType == null) return null;
        TypedExpression result = hidingIRef(arg, piEqType.getExpression());
        return result == null ? null : factory.lam(concreteLamParams, applyAt(factory.app(factory.core(result), args)));
      }

      if (type instanceof CoreSigmaExpression || type instanceof CoreClassCallExpression) {
        CoreParameter typeParams = type instanceof CoreSigmaExpression ? ((CoreSigmaExpression) type).getParameters() : ((CoreClassCallExpression) type).getClassFieldParameters();
        List<CoreClassField> classFields = type instanceof CoreClassCallExpression ? Utils.getNotImplementedField((CoreClassCallExpression) type) : null;

        ConcreteExpression arrayLength = null;
        if (type instanceof CoreClassCallExpression classCall && classCall.getDefinition() == ext.prelude.getDArray() && classFields.size() == 2 && classCall.isImplemented(ext.prelude.getArrayElementsType())) {
          CoreExpression leftType = leftTyped.getType().normalize(NormalizationMode.WHNF);
          CoreExpression rightType = rightTyped.getType().normalize(NormalizationMode.WHNF);
          if (leftType instanceof CoreClassCallExpression leftClassCall && rightType instanceof CoreClassCallExpression rightClassCall) {
            CoreExpression leftLength = leftClassCall.getImplementationHere(ext.prelude.getArrayLength(), leftTyped);
            CoreExpression rightLength = rightClassCall.getImplementationHere(ext.prelude.getArrayLength(), rightTyped);
            boolean ok = false;
            if (leftLength != null && rightLength != null) {
              if (Utils.tryTypecheck(typechecker, tc -> tc.compare(leftLength, rightLength, CMP.EQ, null, false, true, false))) {
                ok = true;
              }
            } else {
              CoreExpression length = leftLength != null ? leftLength : rightLength;
              if (length != null) {
                length = length.normalize(NormalizationMode.WHNF);
                if (length instanceof CoreFieldCallExpression fieldCall && fieldCall.getDefinition() == ext.prelude.getArrayLength() && Utils.tryTypecheck(typechecker, tc -> tc.compare(fieldCall.getArgument(), (leftLength != null ? rightTyped : leftTyped).getExpression(), CMP.EQ, null, false, true, false))) {
                  ok = true;
                }
              }
            }
            if (ok) {
              arrayLength = factory.core((leftLength != null ? leftLength : rightLength).computeTyped());
              typeParams = typechecker.substituteParameters(typeParams, LevelSubstitution.EMPTY, Collections.singletonList(arrayLength));
              classFields.remove(0);
            }
          }
        }

        Set<CoreClassField> propFields = new HashSet<>();
        Map<CoreBinding, CoreExpression> propBindings = new HashMap<>();
        int i = 0;
        for (CoreParameter param = typeParams; param.hasNext(); param = param.getNext(), i++) {
          CoreExpression propType = classFields != null && classFields.get(i).isProperty() ? param.getTypeExpr() : null;
          if (propType == null) {
            propType = Utils.minimizeToProp(param.getTypeExpr());
          }
          if (propType != null) {
            propBindings.put(param.getBinding(), propType);
            if (classFields != null) {
              propFields.add(classFields.get(i));
            }
          }
        }

        ConcreteExpression newArg = arg;
        Map<CoreClassField, PathExpression> superFields = new HashMap<>();
        if (type instanceof CoreClassCallExpression classCall) {
          ConcreteExpression baseExpr = arg instanceof ConcreteClassExtExpression ? ((ConcreteClassExtExpression) arg).getBaseClassExpression() : arg;
          CoreDefinition def = ext.definitionProvider.getCoreDefinition(baseExpr instanceof ConcreteReferenceExpression ? ((ConcreteReferenceExpression) baseExpr).getReferent() : null);
          boolean isSubclass = def instanceof CoreClassDefinition && ((CoreClassDefinition) def).isSubClassOf(classCall.getDefinition());
          if (arg instanceof ConcreteClassExtExpression && !isSubclass) {
            typechecker.getErrorReporter().report(new SubclassError(true, classCall.getDefinition().getRef(), baseExpr));
            return null;
          }

          if (isSubclass) {
            Map<ArendRef, CoclauseData> implMap = new HashMap<>();
            if (arg instanceof ConcreteClassExtExpression) {
              for (ConcreteCoclause coclause : ((ConcreteClassExtExpression) arg).getCoclauses().getCoclauseList()) {
                if (coclause.getImplementation() == null) {
                  typechecker.getErrorReporter().report(new TypecheckingError("Implementation is missing", coclause));
                  return null;
                }

                CoreDefinition implDef = ext.definitionProvider.getCoreDefinition(coclause.getImplementedRef());
                if (implDef instanceof CoreClassDefinition implClass) {
                  if (!((CoreClassDefinition) def).isSubClassOf(implClass)) {
                    typechecker.getErrorReporter().report(new SubclassError(false, def.getRef(), coclause));
                    return null;
                  }

                  TypedExpression superEquality = typechecker.typecheck(factory.appBuilder(factory.ref(ext.prelude.getEqualityRef())).app(factory.ref(implClass.getRef()), false).app(left).app(right).build(), null);
                  if (superEquality == null) {
                    return null;
                  }

                  TypedExpression coclauseResult = checkGoals(typechecker.typecheck(coclause.getImplementation(), superEquality.getExpression()));
                  if (coclauseResult == null) {
                    return null;
                  }

                  boolean added = false;
                  for (CoreClassField field : implClass.getNotImplementedFields()) {
                    if (!classCall.isImplementedHere(field) && !propFields.contains(field)) {
                      if (implMap.putIfAbsent(field.getRef(), new CoclauseData(coclause, false)) == null) {
                        superFields.put(field, new FieldPathExpression(field, factory.core(coclauseResult)));
                        added = true;
                      }
                    }
                  }
                  if (!added) {
                    typechecker.getErrorReporter().report(new RedundantCoclauseError(coclause));
                  }
                } else {
                  if (implMap.putIfAbsent(coclause.getImplementedRef(), new CoclauseData(coclause, true)) != null) {
                    typechecker.getErrorReporter().report(new RedundantCoclauseError(coclause));
                  }
                }
              }
            }

            List<ConcreteExpression> tupleFields = new ArrayList<>(classFields.size());
            List<ArendRef> notImplemented = new ArrayList<>();
            for (CoreClassField field : classFields) {
              if (!classCall.isImplemented(field) && !propFields.contains(field)) {
                CoclauseData data = implMap.remove(field.getRef());
                if (data != null) {
                  if (data.fromField) {
                    tupleFields.add(data.coclause.getImplementation());
                  }
                } else {
                  notImplemented.add(field.getRef());
                }
              }
            }

            for (CoclauseData data : implMap.values()) {
              if (data.fromField) {
                typechecker.getErrorReporter().report(new RedundantCoclauseError(data.coclause));
              }
            }

            if (!notImplemented.isEmpty()) {
              typechecker.getErrorReporter().report(new FieldsImplementationError(false, classCall.getDefinition().getRef(), notImplemented, arg instanceof ConcreteClassExtExpression ? ((ConcreteClassExtExpression) arg).getCoclauses() : marker));
              return null;
            }

            newArg = tupleFields.isEmpty() ? null : tupleFields.size() == 1 ? tupleFields.get(0) : factory.withData(arg.getData()).tuple(tupleFields);
          }
        }

        Map<Integer, Boolean> simpCoeIndices = new HashMap<>(); // true == simp_coe, false == ext
        Set<CoreBinding> bindings = new HashSet<>();
        Set<CoreBinding> dependentBindings = new HashSet<>();
        List<ConcreteParameter> sigmaParams = new ArrayList<>();
        Map<CoreBinding, PathExpression> sigmaRefs = new HashMap<>();
        ConcreteExpression lastSigmaParam = null;
        Set<CoreBinding> totalUsed = new HashSet<>();
        List<Set<CoreBinding>> usedList = new ArrayList<>();
        List<ConcreteLetClause> haveClauses = new ArrayList<>(1);
        List<ConcreteLetClause> letClauses = new ArrayList<>();
        List<PiTreeData> piTreeDataList = new ArrayList<>();
        i = 0;
        for (CoreParameter param = typeParams; param.hasNext(); param = param.getNext(), i++) {
          Set<CoreBinding> used = new HashSet<>();
          CoreBinding paramBinding = param.getBinding();
          boolean isProp = propBindings.containsKey(paramBinding);
          if (!bindings.isEmpty()) {
            if (param.getTypeExpr().processSubexpression(e -> {
              if (!(e instanceof CoreReferenceExpression)) {
                return CoreExpression.FindAction.CONTINUE;
              }
              CoreBinding binding = ((CoreReferenceExpression) e).getBinding();
              if (bindings.contains(binding)) {
                if (!isProp) {
                  if (propBindings.containsKey(binding)) {
                    typechecker.getErrorReporter().report(new TypecheckingError("Non-propositional fields cannot depend on propositional ones", marker));
                    return CoreExpression.FindAction.STOP;
                  }
                  if (dependentBindings.contains(binding)) {
                    typechecker.getErrorReporter().report(new TypecheckingError((type instanceof CoreSigmaExpression ? "\\Sigma types" : "Classes") + " with more than two levels of dependencies are not supported", marker));
                    return CoreExpression.FindAction.STOP;
                  }
                  dependentBindings.add(paramBinding);
                }
                used.add(binding);
              }
              return CoreExpression.FindAction.CONTINUE;
            })) {
              return null;
            }
          }
          bindings.add(paramBinding);
          totalUsed.addAll(used);
          usedList.add(used);

          PathExpression superFieldExpr = classFields == null ? null : superFields.get(classFields.get(i));
          if (superFieldExpr != null) {
            sigmaRefs.put(paramBinding, superFieldExpr);
            piTreeDataList.add(null);
            continue;
          }

          ArendRef sigmaRef = factory.local("p" + (i + 1));
          PiTreeData piTreeData = null;
          if (!isProp) {
            boolean isPi = false;
            ConcreteExpression leftExpr = makeProj(factory, left, i, classFields);
            CoreExpression paramType = param.getTypeExpr().normalize(NormalizationMode.WHNF);
            if (paramType instanceof CorePiExpression && withSimpCoe) {
              List<CoreParameter> sigmaParameters = new ArrayList<>();
              List<ConcreteExpression> leftProjs = new ArrayList<>();
              List<ConcreteExpression> rightProjs = new ArrayList<>();
              List<PathExpression> pathRefs = new ArrayList<>();
              int j = 0;
              for (CoreParameter parameter = typeParams; parameter != param; parameter = parameter.getNext(), j++) {
                if (used.contains(parameter.getBinding())) {
                  sigmaParameters.add(parameter);
                  leftProjs.add(makeProj(factory, left, j, classFields));
                  rightProjs.add(makeProj(factory, right, j, classFields));
                  pathRefs.add(sigmaRefs.get(parameter.getBinding()));
                }
              }

              PiTreeMaker piTreeMaker = new PiTreeMaker(ext, typechecker, factory, letClauses);
              PiTreeRoot piTree = piTreeMaker.make(paramType, sigmaParameters);
              if (piTree == null) return null;
              if (!piTree.subtrees.isEmpty()) {
                piTreeData = new PiTreeData(piTreeMaker, piTree, leftProjs);
                lastSigmaParam = piTreeMaker.makeArgType(piTreeData.tree, false, leftProjs, rightProjs, pathRefs, makeProj(factory, left, j, classFields), makeProj(factory, right, j, classFields), false);
                isPi = true;
              }
            } else if (withSimpCoe) {
              Boolean ok = null;
              if (paramType instanceof CoreFunCallExpression && ((CoreFunCallExpression) paramType).getDefinition() == ext.prelude.getEquality()) {
                if (!used.isEmpty()) ok = true;
              } else if (paramType instanceof CoreSigmaExpression || paramType instanceof CoreClassCallExpression) {
                boolean isSimpCoe = !used.isEmpty();
                Set<CoreBinding> depBindings = isSimpCoe ? null : new HashSet<>();
                ok = isSimpCoe;
                CoreParameter parameters = paramType instanceof CoreSigmaExpression ? ((CoreSigmaExpression) paramType).getParameters() : ((CoreClassCallExpression) paramType).getClassFieldParameters();
                List<CoreClassField> fields = paramType instanceof CoreClassCallExpression ? Utils.getNotImplementedField((CoreClassCallExpression) paramType) : null;
                Set<CoreBinding> bindings1 = new HashSet<>();
                for (CoreParameter parameter = parameters; parameter.hasNext(); parameter = parameter.getNext()) {
                  CoreExpression parameterType = parameter.getTypeExpr();
                  if (!(fields != null && fields.get(i).isProperty() || Utils.isProp(parameterType))) {
                    if (parameterType.findFreeBindings(isSimpCoe ? bindings1 : depBindings) != null) {
                      ok = null;
                      break;
                    }
                    if (!isSimpCoe && parameterType.findFreeBindings(bindings1) != null) {
                      depBindings.add(parameter.getBinding());
                    }
                  }
                  bindings1.add(parameter.getBinding());
                }
              } else if (paramType.toEquality() != null) {
                if (!used.isEmpty()) ok = true;
              }
              if (ok != null) simpCoeIndices.put(sigmaParams.size(), ok);
            }

            if (!isPi && dependentBindings.contains(paramBinding)) {
              CoreBinding binding = used.size() > 1 ? null : used.iterator().next();
              PathExpression pathExpr = binding == null ? null : sigmaRefs.get(binding);
              if (pathExpr == null || !pathExpr.getClass().equals(PathExpression.class)) {
                leftExpr = factory.app(factory.ref(ext.prelude.getCoerceRef()), true, Arrays.asList(makeCoeLambda(typeParams, paramBinding, propBindings.get(paramBinding), used, sigmaRefs, factory), leftExpr, factory.ref(ext.prelude.getRightRef())));
              } else {
                leftExpr = factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(SubstitutionMeta.makeLambda(paramBinding.getTypeExpr(), binding, factory), pathExpr.pathExpression, leftExpr));
              }
            }

            if (!isPi) {
              if (paramType instanceof CorePiExpression && !((CorePiExpression) paramType).getParameters().isExplicit()) {
                List<ConcreteParameter> lamParams = new ArrayList<>();
                List<ConcreteArgument> lamArgs = new ArrayList<>();
                loop:
                for (CoreExpression cur = paramType; cur instanceof CorePiExpression; cur = ((CorePiExpression) cur).getCodomain().normalize(NormalizationMode.WHNF)) {
                  for (CoreParameter parameter = ((CorePiExpression) cur).getParameters(); parameter.hasNext(); parameter = parameter.getNext()) {
                    if (parameter.isExplicit()) {
                      break loop;
                    }
                    ArendRef lamRef = factory.local(ext.renamerFactory.getNameFromBinding(parameter.getBinding(), null));
                    lamParams.add(factory.param(false, lamRef));
                    lamArgs.add(factory.arg(factory.ref(lamRef), false));
                  }
                }
                leftExpr = factory.lam(lamParams, factory.app(leftExpr, lamArgs));
              }
              lastSigmaParam = factory.app(factory.ref(ext.prelude.getEqualityRef()), true, Arrays.asList(leftExpr, makeProj(factory, right, i, classFields)));
            }
            sigmaParams.add(factory.param(Collections.singletonList(sigmaRef), lastSigmaParam));
          }

          ConcreteExpression sigmaRefExpr = factory.ref(sigmaRef);
          if (piTreeData != null && piTreeData.tree.isNonDependent()) {
            BasePiTree piTree = piTreeData.tree;
            List<ConcreteParameter> lamParams = new ArrayList<>(piTree.subtrees.size() + 1);
            List<ConcreteArgument> args = new ArrayList<>(piTree.subtrees.size());
            ArendRef iRef = factory.local("i");
            lamParams.add(factory.param(iRef));
            for (PiTreeNode subtree : piTree.subtrees) {
              ArendRef ref = factory.local(ext.renamerFactory.getNameFromBinding(subtree.parameter.getBinding(), null));
              lamParams.add(factory.param(subtree.parameter.isExplicit(), ref));
              args.add(factory.arg(factory.ref(ref), subtree.parameter.isExplicit()));
            }
            sigmaRefExpr = factory.app(factory.ref(ext.prelude.getPathConRef()), true, Collections.singletonList(factory.lam(lamParams, applyAt(factory.app(sigmaRefExpr, args), iRef))));
          }

          sigmaRefs.put(paramBinding, new PathExpression(sigmaRefExpr));
          piTreeDataList.add(piTreeData);
        }

        if (!simpCoeIndices.isEmpty()) {
          ConcreteFactory argFactory = factory.withData(arg.getData());
          if (newArg instanceof ConcreteGoalExpression) {
            return argFactory.goal(null, null, new GoalSolver() {
              @Override
              public @NotNull Collection<? extends InteractiveGoalSolver> getAdditionalSolvers() {
                return Collections.singletonList(new InteractiveGoalSolver() {
                  @Override
                  public @NotNull String getShortDescription() {
                    return "Replace with tuple";
                  }

                  @Override
                  public boolean isApplicable(@NotNull ConcreteGoalExpression goalExpression, @Nullable CoreExpression expectedType) {
                    return true;
                  }

                  @Override
                  public void solve(@NotNull ExpressionTypechecker typechecker, @NotNull ConcreteGoalExpression goalExpression, @Nullable CoreExpression expectedType, @NotNull ArendUI ui, @NotNull Consumer<ConcreteExpression> callback) {
                    List<ConcreteExpression> goals = new ArrayList<>();
                    for (ConcreteParameter ignored : sigmaParams) {
                      goals.add(argFactory.goal());
                    }
                    callback.accept(argFactory.tuple(goals));
                  }
                });
              }
            });
          } else if (newArg instanceof ConcreteTupleExpression && ((ConcreteTupleExpression) newArg).getFields().size() == sigmaParams.size()) {
            List<? extends ConcreteExpression> oldFields = ((ConcreteTupleExpression) newArg).getFields();
            if (oldFields.isEmpty()) {
              newArg = null;
            } else {
              List<ConcreteExpression> newFields = new ArrayList<>(oldFields.size());
              boolean hasDeferred = false;
              for (int j = 0; j < oldFields.size(); j++) {
                Boolean simpCoe = simpCoeIndices.get(j);
                newFields.add(simpCoe == null && !hasDeferred ? oldFields.get(j) : argFactory.app(hasDeferred ? argFactory.meta("later", ext.laterMeta) : simpCoe ? argFactory.meta("simp_coe", ext.simpCoeMeta) : argFactory.meta("ext", new DeferredMetaDefinition(ext.extMeta, false)), true, Collections.singletonList(oldFields.get(j))));
                if (simpCoe != null) hasDeferred = true;
              }
              newArg = argFactory.tuple(newFields);
            }
          } else if (newArg instanceof ConcreteTupleExpression || sigmaParams.size() != 1) {
            typechecker.getErrorReporter().report(new TypecheckingError("Expected a tuple with " + sigmaParams.size() + " arguments", newArg));
            return null;
          }
        }

        TypedExpression sigmaEqType = typechecker.typecheck(sigmaParams.size() == 1 ? lastSigmaParam : factory.sigma(sigmaParams), null);
        if (sigmaEqType == null) return null;

        ArendRef letRef;
        CoreExpression resultExpr = null;
        ConcreteExpression concreteTuple = null;
        if (newArg != null) {
          TypedExpression result = hidingIRef(newArg, sigmaEqType.getExpression());
          if (result == null) return null;

          resultExpr = result.getExpression().getUnderlyingExpression();
          if (resultExpr instanceof CoreReferenceExpression) {
            letRef = null;
            concreteTuple = factory.core(result);
          } else {
            letRef = factory.local("arg");
            concreteTuple = factory.ref(letRef);
          }

          if (letRef != null) {
            haveClauses.add(factory.letClause(letRef, Collections.emptyList(), null, factory.core(result)));
          }
        }

        List<ConcreteExpression> fields = new ArrayList<>();
        Map<CoreBinding, PathExpression> fieldsMap = new HashMap<>();
        List<ConcreteExpression> fieldsList = new ArrayList<>();
        i = 0;
        int i1 = 0;
        for (CoreParameter param = typeParams; param.hasNext(); param = param.getNext(), i++) {
          ConcreteExpression field;
          ConcreteExpression fieldWithAt = null;
          PathExpression pathExpr = classFields == null ? null : superFields.get(classFields.get(i));
          CoreBinding paramBinding = param.getBinding();
          boolean useLet;
          if (pathExpr != null) {
            fieldWithAt = pathExpr.applyAt(iRef, factory, ext);
            ArendRef pRef = factory.local("i");
            field = applyPath(pRef, pathExpr.applyAt(pRef, factory, ext));
            useLet = false;
          } else if (propBindings.containsKey(paramBinding)) {
            field = factory.app(factory.ref(ext.propDPI.getRef()), true, Arrays.asList(makeCoeLambda(typeParams, paramBinding, propBindings.get(paramBinding), usedList.get(i), fieldsMap, factory), makeProj(factory, left, i, classFields), makeProj(factory, right, i, classFields)));
            useLet = true;
          } else {
            boolean isDependent = dependentBindings.contains(paramBinding);
            if (isDependent) {
              useLet = true;
            } else {
              if (sigmaParams.size() == 1) {
                useLet = false;
              } else {
                useLet = resultExpr != null && useLet(resultExpr, i1);
              }
            }

            if (concreteTuple == null) {
              concreteTuple = factory.tuple();
            }
            ConcreteExpression proj = sigmaParams.size() == 1 ? concreteTuple : factory.proj(concreteTuple, i1);
            if (piTreeDataList.get(i) != null) {
              PiTreeMaker piTreeMaker = piTreeDataList.get(i).maker;
              PiTreeRoot piTree = piTreeDataList.get(i).tree;
              if (piTree.isNonDependent()) {
                useLet = true;
                List<ConcreteParameter> lamParams = new ArrayList<>(piTree.subtrees.size() + 1);
                List<ConcreteArgument> args = new ArrayList<>(piTree.subtrees.size());
                ArendRef iRef = factory.local("i");
                lamParams.add(factory.param(iRef));
                for (PiTreeNode subtree : piTree.subtrees) {
                  ArendRef ref = factory.local(ext.renamerFactory.getNameFromBinding(subtree.parameter.getBinding(), null));
                  lamParams.add(factory.param(subtree.parameter.isExplicit(), ref));
                  args.add(factory.arg(factory.ref(ref), subtree.parameter.isExplicit()));
                }
                fieldWithAt = factory.lam(lamParams.subList(1, lamParams.size()), applyAt(factory.app(proj, args), this.iRef));
                proj = factory.app(factory.ref(ext.prelude.getPathConRef()), true, Collections.singletonList(factory.lam(lamParams, applyAt(factory.app(proj, args), iRef))));
              } else {
                if (!(coreLeft instanceof CoreReferenceExpression)) {
                  ArendRef projRef = factory.local("l");
                  letClauses.add(factory.letClause(projRef, Collections.emptyList(), null, left));
                  left = factory.ref(projRef);
                }

                List<ConcreteExpression> rightRefs = new ArrayList<>();
                List<PathExpression> pathRefs = new ArrayList<>();
                List<ConcreteCaseArgument> caseArgs = new ArrayList<>();
                List<ConcretePattern> casePatterns = new ArrayList<>();
                ArendRef lastCaseRef = factory.local("a");
                int j = 0;
                for (CoreParameter parameter = typeParams; parameter != param; parameter = parameter.getNext(), j++) {
                  if (usedList.get(i).contains(parameter.getBinding())) {
                    ArendRef rightRef = factory.local("r" + (j + 1));
                    rightRefs.add(factory.ref(rightRef));
                    caseArgs.add(factory.caseArg(makeProj(factory, right, j, classFields), rightRef, null));

                    ArendRef pathRef = factory.local("q" + (j + 1));
                    pathRefs.add(new PathExpression(factory.ref(pathRef)));
                    caseArgs.add(factory.caseArg(fieldsList.get(j), pathRef, factory.app(factory.ref(ext.prelude.getEqualityRef()), true, Arrays.asList(makeProj(factory, left, j, classFields), factory.ref(rightRef)))));

                    casePatterns.add(factory.refPattern(null, null));
                    casePatterns.add(factory.conPattern(ext.prelude.getIdpRef()));
                  }
                }

                ArendRef rightFunRef = factory.local("f");
                ConcreteExpression leftFun = makeProj(factory, left, j, classFields);
                caseArgs.add(factory.caseArg(makeProj(factory, right, j, classFields), rightFunRef, piTreeMaker.makeConcrete(piTree, true, rightRefs)));
                caseArgs.add(factory.caseArg(proj, null, piTreeMaker.makeArgType(piTree, true, piTreeDataList.get(i).leftProjs, rightRefs, pathRefs, leftFun, factory.ref(rightFunRef), false)));

                casePatterns.add(factory.refPattern(null, null));
                casePatterns.add(factory.refPattern(lastCaseRef, null));

                ConcreteExpression caseResultType = factory.app(factory.ref(ext.prelude.getEqualityRef()), true, Arrays.asList(piTreeMaker.makeCoe(piTree, true, pathRefs, leftFun), factory.ref(rightFunRef)));
                proj = factory.caseExpr(false, caseArgs, caseResultType, null, factory.clause(casePatterns, factory.app(factory.meta("ext", ExtMeta.this), true, Collections.singletonList(factory.ref(lastCaseRef)))));
              }
            }

            field = isDependent ? factory.appBuilder(factory.ref(ext.pathOver.getRef())).app(makeCoeLambda(typeParams, paramBinding, propBindings.get(paramBinding), usedList.get(i), fieldsMap, factory), false).app(proj).build() : proj;
            i1++;
          }

          if (useLet && totalUsed.contains(paramBinding)) {
            ArendRef argLetRef = factory.local("h" + i1);
            letClauses.add(factory.letClause(argLetRef, Collections.emptyList(), null, field));
            field = factory.ref(argLetRef);
          }
          fields.add(addImplicitLambda(fieldWithAt == null ? applyAt(field) : fieldWithAt, paramBinding.getTypeExpr(), factory));
          fieldsMap.put(paramBinding, pathExpr != null ? pathExpr : new PathExpression(field));
          fieldsList.add(field);
        }

        ConcreteExpression concreteResult;
        if (type instanceof CoreClassCallExpression) {
          List<ConcreteClassElement> classElements = new ArrayList<>(classFields.size());
          if (arrayLength != null) {
            classElements.add(factory.implementation(ext.prelude.getArrayLengthRef(), arrayLength));
          }
          for (int j = 0; j < classFields.size(); j++) {
            classElements.add(factory.implementation(classFields.get(j).getRef(), fields.get(j)));
          }
          concreteResult = factory.newExpr(factory.classExt(factory.ref(((CoreClassCallExpression) type).getDefinition().getRef()), classElements));
        } else {
          concreteResult = factory.tuple(fields);
        }

        for (PiTreeData piTreeData : piTreeDataList) {
          if (piTreeData != null) piTreeData.maker.removeUnusedClauses(piTreeData.tree);
        }

        ConcreteExpression let = letClauses.isEmpty() ? concreteResult : factory.letExpr(false, false, letClauses, concreteResult);
        return haveClauses.isEmpty() ? let : factory.letExpr(true, false, haveClauses, let);
      }

      typechecker.getErrorReporter().report(new TypeError(typechecker.getExpressionPrettifier(), "Cannot apply extensionality", type, marker));
      return null;
    }
  }

  private enum Kind { PROP, NOT_PROP }

  private static boolean atLeastSet(CoreExpression type) {
    type = type.normalize(NormalizationMode.WHNF);
    CoreLevel level = type instanceof CoreUniverseExpression ? ((CoreUniverseExpression) type).getSort().getHLevel() : null;
    return level != null && (level.isClosed() && level.getConstant() >= 0 || level.getMaxConstant() >= 0 || level.getConstant() >= 1);
  }

  private static DefermentChecker.Result checkStuckExpression(CoreExpression expr) {
    CoreExpression stuck = expr.getStuckExpression();
    return stuck instanceof CoreInferenceReferenceExpression && ((CoreInferenceReferenceExpression) stuck).getVariable() != null ? DefermentChecker.Result.AFTER_LEVELS : null;
  }

  public static final DefermentChecker defermentChecker = (typechecker, data) -> {
    if (data.getUserData() == DefermentChecker.Result.AFTER_LEVELS) return DefermentChecker.Result.DO_NOT_DEFER;

    CoreExpression expectedType = data.getExpectedType().normalize(NormalizationMode.WHNF);
    DefermentChecker.Result result = checkStuckExpression(expectedType);
    if (result != null) {
      data.setExpectedType(expectedType);
      return result;
    }

    CoreFunCallExpression equality = Utils.toEquality(expectedType, typechecker.getErrorReporter(), data.getMarker());
    if (equality == null) return null;
    data.setExpectedType(equality);
    CoreExpression type = equality.getDefCallArguments().get(0).normalize(NormalizationMode.WHNF);
    result = checkStuckExpression(type);
    if (result != null) return result;

    if (type instanceof CoreUniverseExpression) {
      CoreLevel level = ((CoreUniverseExpression) type).getSort().getHLevel();
      if (level != null && level.isClosed()) return DefermentChecker.Result.DO_NOT_DEFER;
      if (atLeastSet(equality.getDefCallArguments().get(1).computeType()) || atLeastSet(equality.getDefCallArguments().get(2).computeType())) {
        data.setUserData(Kind.NOT_PROP);
        return DefermentChecker.Result.DO_NOT_DEFER;
      }
    }

    return type instanceof CoreSigmaExpression ? DefermentChecker.Result.AFTER_LEVELS : DefermentChecker.Result.DO_NOT_DEFER;
  };

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteSourceNode marker = contextData.getMarker();
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    CoreFunCallExpression equality = Utils.toEquality(contextData.getExpectedType(), errorReporter, marker);
    if (equality == null) return null;

    List<? extends ConcreteArgument> args = contextData.getArguments();
    ConcreteFactory factory = ext.factory.withData(marker);
    CoreExpression type = equality.getDefCallArguments().get(0);
    if (contextData.getUserData() != Kind.NOT_PROP && Utils.isProp(type)) {
      if (!args.isEmpty()) {
        errorReporter.report(new IgnoredArgumentError(args.get(0).getExpression()));
      }
      return typechecker.typecheck(factory.app(factory.ref(ext.propIsProp.getRef()), true, Arrays.asList(factory.hole(), factory.hole())), contextData.getExpectedType());
    }

    if (args.isEmpty()) {
      errorReporter.report(new MissingArgumentsError(1, marker));
      return null;
    }

    CoreExpression origNormType = type.normalize(NormalizationMode.WHNF);
    CoreExpression normType = Utils.unfoldType(origNormType);
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
        return typechecker.typecheck(letRef == null ? result : factory.letExpr(true, false, Collections.singletonList(factory.letClause(letRef, Collections.emptyList(), null, concreteArg)), result), contextData.getExpectedType());
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
    return typechecker.typecheck(factory.app(factory.ref(ext.prelude.getPathConRef()), true, Collections.singletonList(factory.lam(Collections.singletonList(factory.param(iRef)), factory.meta("ext_result", new MetaDefinition() {
      @Override
      public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        ExtGenerator generator = new ExtGenerator(typechecker, factory, marker, iRef);
        ConcreteExpression result = generator.generate(arg, normType, equality.getDefCallArguments().get(1), equality.getDefCallArguments().get(2));
        return result == null ? null : generator.goalExpr != null ? generator.goalExpr.computeTyped() : typechecker.typecheck(result, result instanceof ConcreteGoalExpression ? null : origNormType);
      }
    })))), contextData.getExpectedType());
  }
}
