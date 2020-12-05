package org.arend.lib.meta.pi_tree;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CorePiExpression;
import org.arend.ext.core.expr.CoreReferenceExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.core.ops.SubstitutionPair;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class PiTreeMaker {
  private final StdExtension ext;
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;
  private final List<ConcreteLetClause> clauses;
  private List<ConcreteParameter> lamParams;
  private List<SubstitutionPair> substitution;
  private int index = 1;

  public PiTreeMaker(StdExtension ext, ExpressionTypechecker typechecker, ConcreteFactory factory, List<ConcreteLetClause> clauses) {
    this.ext = ext;
    this.typechecker = typechecker;
    this.factory = factory;
    this.clauses = clauses;
  }

  private BasePiTree make(boolean isRoot, CoreParameter parameter, CoreExpression expr) {
    List<CoreParameter> params = new ArrayList<>();
    expr = expr.normalize(NormalizationMode.WHNF);
    CoreExpression codomain = expr;
    loop:
    while (codomain instanceof CorePiExpression) {
      CorePiExpression piExpr = (CorePiExpression) codomain;
      Set<? extends CoreBinding> codomainFreeVars = piExpr.getCodomain().findFreeBindings();
      for (CoreParameter param = piExpr.getParameters(); param.hasNext(); param = param.getNext()) {
        if (codomainFreeVars.contains(param.getBinding())) {
          break loop;
        }
      }
      for (CoreParameter param = piExpr.getParameters(); param.hasNext(); param = param.getNext()) {
        params.add(param);
      }
      codomain = piExpr.getCodomain();
    }

    Set<? extends CoreBinding> freeVars = expr.findFreeBindings();
    List<Integer> indices = new ArrayList<>(freeVars.size());
    for (int i = 0; i < substitution.size(); i++) {
      if (freeVars.contains(substitution.get(i).binding)) {
        indices.add(i);
      }
    }

    ConcreteExpression concrete;
    boolean useLet;
    if (indices.isEmpty()) {
      if (!isRoot) {
        params.clear();
        codomain = expr;
      }
      concrete = factory.core(codomain.computeTyped());
      useLet = !(expr instanceof CoreReferenceExpression);
    } else {
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
      useLet = !(result.getExpression() instanceof CoreReferenceExpression);
    }

    ConcreteExpression altHead;
    if (useLet) {
      ArendRef letRef = factory.local("T" + index++);
      clauses.add(factory.letClause(letRef, Collections.emptyList(), null, concrete));
      altHead = factory.ref(letRef);
    } else {
      altHead = concrete;
    }

    List<PiTreeNode> subtrees = new ArrayList<>(params.size());
    for (CoreParameter param : params) {
      PiTreeNode subtree = (PiTreeNode) make(false, param, param.getTypeExpr());
      if (subtree == null) return null;
      subtrees.add(subtree);
    }
    return isRoot ? new PiTreeRoot(concrete, altHead, indices, subtrees) : new PiTreeNode(parameter, concrete, altHead, indices, subtrees);
  }

  public PiTreeRoot make(CoreExpression expr, List<CoreParameter> parameters) {
    lamParams = new ArrayList<>(parameters.size());
    substitution = new ArrayList<>(parameters.size());
    for (int i = 0; i < parameters.size(); i++) {
      CoreParameter parameter = parameters.get(i);
      ArendRef ref = factory.local("x" + (i + 1));
      lamParams.add(factory.param(true, Collections.singletonList(ref), factory.core(parameter.getTypedType())));
      substitution.add(new SubstitutionPair(parameter.getBinding(), factory.ref(ref)));
    }
    return (PiTreeRoot) make(true, null, expr);
  }


  public ConcreteExpression makeConcrete(BasePiTree tree, boolean useLet, List<ConcreteExpression> args) {
    return makeConcrete(tree, useLet, args, args, true);
  }

  private ConcreteExpression makeConcrete(BasePiTree tree, boolean useLet, List<ConcreteExpression> evenArgs, List<ConcreteExpression> oddArgs, boolean isEven) {
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

  public ConcreteExpression makeCoe(BasePiTree tree, boolean useHead, boolean useLet, List<PathExpression> pathRefs, ConcreteExpression arg) {
    ArendRef coeRef = factory.local("i");
    ConcreteExpression coeLam = factory.lam(Collections.singletonList(factory.param(coeRef)), factory.meta("ext_coe", new MetaDefinition() {
      @Override
      public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        List<ConcreteExpression> args = new ArrayList<>();
        for (PathExpression pathRef : pathRefs) {
          args.add(pathRef.applyAt(coeRef, factory, ext));
        }
        return typechecker.typecheck(useHead ? factory.app(useLet ? tree.altHead : tree.head, true, args) : makeConcrete(tree, useLet, args), null);
      }
    }));
    return factory.app(factory.ref(ext.prelude.getCoerce().getRef()), true, Arrays.asList(coeLam, arg, factory.ref(ext.prelude.getRight().getRef())));
  }

  private ConcreteExpression etaExpand(BasePiTree tree, ConcreteExpression fun, List<ConcreteArgument> args, boolean insertCoe, boolean useLet, List<PathExpression> pathRefs) {
    List<ConcreteArgument> expandedArgs = new ArrayList<>(args.size());
    for (int i = 0; i < args.size(); i++) {
      BasePiTree subtree = tree.subtrees.get(i);
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
      PathExpression pathExpr = pathRefs.get(tree.indices.get(0));
      if (pathExpr.getClass().equals(PathExpression.class)) {
        return factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(useLet ? tree.altHead : tree.head, pathExpr.pathExpression, result));
      }
    }

    return makeCoe(tree, true, useLet, pathRefs, result);
  }

  public ConcreteExpression makeArgType(BasePiTree tree, boolean useLet, List<ConcreteExpression> leftRefs, List<ConcreteExpression> rightRefs, List<PathExpression> pathRefs, ConcreteExpression leftFun, ConcreteExpression rightFun) {
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
