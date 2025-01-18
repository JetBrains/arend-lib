package org.arend.lib.meta.pi_tree;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
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
import org.arend.lib.meta.util.SubstitutionMeta;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class PiTreeMaker {
  private final StdExtension ext;
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;
  private final List<ConcreteLetClause> clauses;
  private final Map<ArendRef, ConcreteLetClause> clauseMap = new HashMap<>();
  private List<ConcreteParameter> lamParams;
  private List<SubstitutionPair> substitution;
  private Set<CoreBinding> substBindings;
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
    int k = lamParams.size();
    List<Integer> indices1 = new ArrayList<>();
    loop:
    while (codomain instanceof CorePiExpression piExpr) {
      Set<? extends CoreBinding> codomainFreeVars = piExpr.getCodomain().findFreeBindings();
      for (CoreParameter param = piExpr.getParameters(); param.hasNext(); param = param.getNext(), k++) {
        ArendRef lamRef = factory.local("x" + (k + 1));
        lamParams.add(factory.param(lamRef));
        substitution.add(new SubstitutionPair(param.getBinding(), factory.ref(lamRef)));

        if (codomainFreeVars.contains(param.getBinding())) {
          if (isRoot && param.getTypeExpr().findFreeBindings(substBindings) == null) {
            indices1.add(k);
          } else {
            break loop;
          }
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
    indices.addAll(indices1);

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

      TypedExpression result = typechecker.typecheck(factory.lam(redLamParams, factory.meta("ext_sigma_pi_param", new SubstitutionMeta(codomain, redSubstitution))), null);
      if (result == null) return null;
      concrete = factory.core(result);
      useLet = !(result.getExpression() instanceof CoreReferenceExpression);
    }

    ConcreteExpression altHead;
    if (useLet) {
      ArendRef letRef = factory.local("T" + index++);
      ConcreteLetClause clause = factory.letClause(letRef, Collections.emptyList(), null, concrete);
      clauses.add(clause);
      clauseMap.put(letRef, clause);
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
    return isRoot ? new PiTreeRoot(concrete, altHead, indices, subtrees, indices.size() == indices1.size()) : new PiTreeNode(parameter, concrete, altHead, indices, subtrees);
  }

  public PiTreeRoot make(CoreExpression expr, List<CoreParameter> parameters) {
    lamParams = new ArrayList<>(parameters.size());
    substitution = new ArrayList<>(parameters.size());
    substBindings = new HashSet<>();
    for (int i = 0; i < parameters.size(); i++) {
      CoreParameter parameter = parameters.get(i);
      ArendRef ref = factory.local("x" + (i + 1));
      lamParams.add(factory.param(true, Collections.singletonList(ref), factory.core(parameter.getTypedType())));
      substitution.add(new SubstitutionPair(parameter.getBinding(), factory.ref(ref)));
      substBindings.add(parameter.getBinding());
    }
    return (PiTreeRoot) make(true, null, expr);
  }

  public void removeUnusedClauses(PiTreeRoot root) {
    Set<ConcreteLetClause> unusedClauses = new HashSet<>();
    getUnusedClauses(root, unusedClauses);
    clauses.removeAll(unusedClauses);
  }

  private void getUnusedClauses(BasePiTree piTree, Set<ConcreteLetClause> clauses) {
    if (!piTree.isAltHeadUsed() && piTree.getAltHead() instanceof ConcreteReferenceExpression) {
      ConcreteLetClause clause = clauseMap.get(((ConcreteReferenceExpression) piTree.getAltHead()).getReferent());
      if (clause != null) clauses.add(clause);
    }
    for (PiTreeNode subtree : piTree.subtrees) {
      getUnusedClauses(subtree, clauses);
    }
  }


  public ConcreteExpression makeConcrete(PiTreeRoot tree, boolean useLet, List<ConcreteExpression> args) {
    return makeConcrete(tree, useLet, args, args, true);
  }

  private ConcreteExpression makeConcrete(BasePiTree tree, boolean useLet, List<ConcreteExpression> evenArgs, List<ConcreteExpression> oddArgs, boolean isEven) {
    List<ArendRef> piRefs;
    if (tree instanceof PiTreeRoot) {
      evenArgs = new ArrayList<>(evenArgs);
      oddArgs = new ArrayList<>(oddArgs);
      piRefs = new ArrayList<>(tree.subtrees.size());
      for (int i = 0; i < tree.subtrees.size(); i++) {
        ArendRef piRef = factory.local("y" + (i + 1));
        piRefs.add(piRef);
        evenArgs.add(factory.ref(piRef));
        oddArgs.add(factory.ref(piRef));
      }
    } else {
      piRefs = null;
    }

    ConcreteExpression result = useLet ? tree.getAltHead() : tree.head;
    if (!tree.indices.isEmpty()) {
      List<ConcreteExpression> headArgs = new ArrayList<>(tree.indices.size());
      for (Integer index : tree.indices) {
        headArgs.add((isEven ? evenArgs : oddArgs).get(index));
      }
      result = factory.app(result, true, headArgs);
    }

    for (int i = tree.subtrees.size() - 1; i >= 0; i--) {
      ConcreteExpression domain = makeConcrete(tree.subtrees.get(i), useLet, evenArgs, oddArgs, !isEven);
      boolean isExplicit = tree.subtrees.get(i).parameter.isExplicit();
      result = piRefs == null ? (isExplicit ? factory.arr(domain, result) : factory.pi(Collections.singletonList(factory.param(false, Collections.singletonList(null), domain)), result)) : factory.pi(Collections.singletonList(factory.param(isExplicit, Collections.singletonList(piRefs.get(i)), domain)), result);
    }
    return result;
  }

  public ConcreteExpression makeCoe(PiTreeRoot tree, boolean useLet, List<PathExpression> pathRefs, ConcreteExpression arg) {
    ConcreteExpression result = makeCoe(tree, null, useLet, pathRefs, arg);

    int n = 0;
    for (PiTreeNode subtree : tree.subtrees) {
      if (subtree.parameter.isExplicit()) {
        break;
      }
      n++;
    }
    if (n == 0) {
      return result;
    }

    List<ConcreteParameter> params = new ArrayList<>(n);
    List<ConcreteExpression> args = new ArrayList<>(n);
    for (int i = 0; i < n; i++) {
      ArendRef ref = factory.local(ext.renamerFactory.getNameFromBinding(tree.subtrees.get(i).parameter.getBinding(), "x"));
      params.add(factory.param(false, ref));
      args.add(factory.ref(ref));
    }
    return factory.lam(params, factory.app(result, false, args));
  }

  private ConcreteExpression makeCoe(BasePiTree tree, List<ConcreteArgument> headArgs, boolean useLet, List<PathExpression> pathRefs, ConcreteExpression arg) {
    assert headArgs != null || tree instanceof PiTreeRoot;

    boolean needCoe = false;
    for (Integer index : tree.indices) {
      if (index < pathRefs.size()) {
        needCoe = true;
        break;
      }
    }

    if (!needCoe) {
      return arg;
    }

    ArendRef coeRef = factory.local("i");
    ConcreteExpression coeLam = factory.lam(Collections.singletonList(factory.param(coeRef)), factory.meta("ext_coe", new MetaDefinition() {
      @Override
      public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        List<ConcreteExpression> args = new ArrayList<>();
        for (Integer index : tree.indices) {
          if (index < pathRefs.size()) {
            args.add(pathRefs.get(index).applyAt(coeRef, factory, ext));
          } else if (headArgs != null) {
            args.add(headArgs.get(index - pathRefs.size()).getExpression());
          }
        }
        return typechecker.typecheck(headArgs != null ? factory.app(useLet ? tree.getAltHead() : tree.head, true, args) : makeConcrete((PiTreeRoot) tree, useLet, args), null);
      }
    }));
    return factory.app(factory.ref(ext.prelude.getCoerceRef()), true, Arrays.asList(coeLam, arg, factory.ref(ext.prelude.getRightRef())));
  }

  private ConcreteExpression etaExpand(BasePiTree tree, ConcreteExpression fun, List<ConcreteArgument> args, List<ConcreteArgument> topArgs, boolean insertCoe, boolean useLet, List<PathExpression> pathRefs) {
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
      expandedArgs.add(factory.arg(factory.lam(lamParams, etaExpand(subtree, args.get(i).getExpression(), lamRefs, topArgs, !insertCoe, useLet, pathRefs)), args.get(i).isExplicit()));
    }

    ConcreteExpression result = factory.app(fun, expandedArgs);
    if (!insertCoe || tree.indices.isEmpty()) {
      return result;
    }

    if (tree.indices.size() == 1 && tree.indices.get(0) < pathRefs.size()) {
      PathExpression pathExpr = pathRefs.get(tree.indices.get(0));
      if (pathExpr.getClass().equals(PathExpression.class)) {
        return factory.app(factory.ref(ext.transport.getRef()), true, Arrays.asList(useLet ? tree.getAltHead() : tree.head, pathExpr.pathExpression, result));
      }
    }

    return makeCoe(tree, topArgs, useLet, pathRefs, result);
  }

  public ConcreteExpression makeArgType(PiTreeRoot tree, boolean useLet, List<ConcreteExpression> leftRefs, List<ConcreteExpression> rightRefs, List<PathExpression> pathRefs, ConcreteExpression leftFun, ConcreteExpression rightFun, boolean genType) {
    leftRefs = new ArrayList<>(leftRefs);
    rightRefs = new ArrayList<>(rightRefs);
    List<ConcreteArgument> piRefs = new ArrayList<>(tree.subtrees.size());
    List<ConcreteParameter> piParams = new ArrayList<>(tree.subtrees.size());
    for (int i = 0; i < tree.subtrees.size(); i++) {
      ArendRef piRef = factory.local(ext.renamerFactory.getNameFromBinding(tree.subtrees.get(i).parameter.getBinding(), "s"));
      ConcreteExpression piRefExpr = factory.ref(piRef);
      leftRefs.add(piRefExpr);
      rightRefs.add(piRefExpr);
      piRefs.add(factory.arg(piRefExpr, tree.subtrees.get(i).parameter.isExplicit()));
      piParams.add(factory.param(tree.subtrees.get(i).parameter.isExplicit(), Collections.singletonList(piRef), makeConcrete(tree.subtrees.get(i), useLet, leftRefs, rightRefs, true)));
    }

    index = 1;
    ConcreteExpression leftArg = etaExpand(tree, leftFun, piRefs, piRefs, true, useLet, pathRefs);
    index = 1;
    ConcreteExpression rightArg = etaExpand(tree, rightFun, piRefs, piRefs, false, useLet, pathRefs);
    List<ConcreteArgument> args = new ArrayList<>(3);
    if (genType) {
      List<ConcreteExpression> headArgs = new ArrayList<>();
      for (Integer i : tree.indices) {
        headArgs.add(rightRefs.get(i));
      }
      args.add(factory.arg(factory.app(useLet ? tree.getAltHead() : tree.head, true, headArgs), false));
    }
    args.add(factory.arg(leftArg, true));
    args.add(factory.arg(rightArg, true));
    return factory.pi(piParams, factory.app(factory.ref(ext.prelude.getEqualityRef()), args));
  }
}
