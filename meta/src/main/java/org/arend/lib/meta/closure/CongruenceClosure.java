package org.arend.lib.meta.closure;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteAppExpression;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.util.Pair;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

public class CongruenceClosure<V extends CoreExpression> implements BinaryRelationClosure<V> {
  private final ValuesEx terms;

  private final DisjointSet<VarId> varsEquivClasses = new DisjointSetImpl<>();
  private final EquivalenceClosure<VarId> equivalenceClosure;
  private final Map<VarId, Pair<VarId, VarId>> varDefs = new HashMap<>();
  private final Map<VarId, List<VarId>> occurrenceLists = new HashMap<>();
  private final Map<Integer, List<VarId>> congrTable = new HashMap<>();

  private final Function<List<EqProofOrElement>, ConcreteExpression> congrLemma;

  public static class EqualityIsEquivProof {
    public ConcreteExpression refl;
    public ConcreteExpression sym;
    public ConcreteExpression trans;

    public EqualityIsEquivProof(ConcreteExpression refl, ConcreteExpression sym, ConcreteExpression trans) {
      this.refl = refl;
      this.sym = sym;
      this.trans = trans;
    }
  }

  public CongruenceClosure(ExpressionTypechecker typechecker, ConcreteSourceNode marker, Function<List<EqProofOrElement>, ConcreteExpression> congrLemma, EqualityIsEquivProof equalityIsEquivLemma, ConcreteFactory factory) {
    this.congrLemma = congrLemma;
    this.terms = new ValuesEx(typechecker, marker);
    this.equivalenceClosure = new EquivalenceClosure<>(equalityIsEquivLemma.refl, equalityIsEquivLemma.sym, equalityIsEquivLemma.trans, factory);
  }

  private void initAppExprVar(VarId var, VarId parentVar) {
    List<VarId> occurList = occurrenceLists.get(var);
    if (occurList == null) {
      occurList = new ArrayList<>(Collections.singletonList(parentVar));
      occurrenceLists.put(var, occurList);
    } else {
      occurList.add(parentVar);
    }
  }

  private int addTerm(CoreExpression term, VarId parentVar, Queue<Pair<CoreExpression, Integer>> termsToSplit) {
    var normTerm = term.normalize(NormalizationMode.WHNF);
    int numOfTerms = terms.getValues().size();
    int termInd = terms.addValue(normTerm);

    if (parentVar != null) {
      initAppExprVar(new VarId(termInd, -1), parentVar);
    }

    if (terms.getValues().size() != numOfTerms) {
      termsToSplit.add(new Pair<>(normTerm, termInd));
    }

    return termInd;
  }

  private Integer splitIntoSubterms(V term) {
    Queue<Pair<CoreExpression, Integer>> termsToSplit = new ArrayDeque<>();
    Set<VarId> toBeAddedToCongrTable = new HashSet<>();

    int inputTermVar = addTerm(term, null, termsToSplit);

    while (!termsToSplit.isEmpty()) {
      Pair<CoreExpression, Integer> subtermPair = termsToSplit.poll();
      CoreExpression subterm = subtermPair.proj1;
      int var = subtermPair.proj2;

      toBeAddedToCongrTable.add(new VarId(var, -1));
      if (subterm instanceof CoreAppExpression) {
        CoreExpression func = ((CoreAppExpression) subterm).getFunction();
        CoreExpression arg = ((CoreAppExpression) subterm).getArgument();
        CoreExpression funcType = func.computeType();
        boolean doSplitting = true;

        if (funcType instanceof CorePiExpression) {
          doSplitting = !((CorePiExpression) funcType).getCodomain().findFreeBinding(((CorePiExpression) funcType).getParameters().getBinding());
        }

        if (doSplitting) {
          int funcVar = addTerm(func, new VarId(var, -1), termsToSplit);
          int argVar = addTerm(arg, new VarId(var, -1), termsToSplit);

          varDefs.put(new VarId(var, -1), new Pair<>(new VarId(funcVar, -1), new VarId(argVar, -1)));
        }
      } else if (subterm instanceof CoreDefCallExpression && !(subterm instanceof CoreFieldCallExpression)) {
        int numArgs = ((CoreDefCallExpression) subterm).getDefCallArguments().size();
        List<VarId> prefixVars = terms.getVarIds(subterm);
        VarId appVar = prefixVars.get(0);

        for (int i = 0; i < numArgs; ++i) {
          int argVar = addTerm(((CoreDefCallExpression) subterm).getDefCallArguments().get(numArgs - 1 - i), appVar, termsToSplit);
          VarId funcVar = prefixVars.get(i + 1);
          boolean stop = funcVar != null;
          if (funcVar == null) {
            funcVar = new VarId(var, i);
          }
          varDefs.put(appVar, new Pair<>(funcVar, new VarId(argVar, -1)));
          initAppExprVar(funcVar, appVar);
          toBeAddedToCongrTable.add(appVar);
          if (stop) {
            break;
          }
          if (i == numArgs - 1) {
            toBeAddedToCongrTable.add(funcVar);
          }
          appVar = funcVar;
        }
      }
    }

    Queue<Equality> pending = new ArrayDeque<>();
    for (VarId var : toBeAddedToCongrTable) {
      addToCongrTable(var, pending);
    }

    addEqualities(pending);
    return inputTermVar;
  }

  private boolean areCongruent(VarId var1, VarId var2, boolean canBeEqual) {
    if (canBeEqual && varsEquivClasses.find(var1).equals(varsEquivClasses.find(var2))) {
      return true;
    }

    Pair<VarId, VarId> def1 = varDefs.get(var1);
    Pair<VarId, VarId> def2 = varDefs.get(var2);

    if ((def1 == null) != (def2 == null)) return false;

    if (def1 == null) return false;

    return varsEquivClasses.find(def1.proj2).equals(varsEquivClasses.find(def2.proj2)) &&
        areCongruent(def1.proj1, def2.proj1, true);
  }

  public static class EqProofOrElement {
    public ConcreteExpression eqProofOrElement;
    public boolean isElement;

    public EqProofOrElement(ConcreteExpression eqProofOrElement, boolean isRefl) {
      this.eqProofOrElement = eqProofOrElement;
      this.isElement = isRefl;
    }
  }

  private ConcreteExpression getConcreteTerm(VarId var) {
    CoreExpression term = terms.getValue(var.value);
    ConcreteFactory factory = equivalenceClosure.factory;
    if (var.prefix == -1) {
      return factory.core(term.computeTyped());
    }
    if (!(term instanceof CoreDefCallExpression)) return null;
    int numArgs = ((CoreDefCallExpression) term).getDefCallArguments().size();
    List<ConcreteArgument> args = ((CoreDefCallExpression) term).getDefCallArguments().subList(0, numArgs - 1 - var.prefix).stream().map(x -> factory.arg(factory.core(x.computeTyped()), true)).collect(Collectors.toList());
    return factory.app(factory.ref(((CoreDefCallExpression) term).getDefinition().getRef()), args);
  }

  private int getNumberOfInvs(List<ConcreteExpression> path) {
    int numOfInvs = 0;
    for (ConcreteExpression proof : path) {
      if (proof instanceof ConcreteAppExpression && ((ConcreteAppExpression) proof).getFunction().equals(equivalenceClosure.sym)) {
        ++numOfInvs;
      }
    }
    return numOfInvs;
  }

  private boolean shouldBeInverted(VarId var1, VarId var2) {
    List<ConcreteExpression> path12 = equivalenceClosure.getPath(var1, var2);
    List<ConcreteExpression> path21 = equivalenceClosure.getPath(var2, var1);
    return (path12 != null && path21 != null && getNumberOfInvs(path12) > getNumberOfInvs(path21));
  }

  private EqProofOrElement checkEquality(VarId var1, VarId var2) {
    if (var1.equals(var2)) {
      return new EqProofOrElement(getConcreteTerm(var1), true);
    }
    return new EqProofOrElement(equivalenceClosure.checkRelation(var1, var2), false);
  }

  private boolean shouldInvertCongrProof(VarId var1, VarId var2) {
    Pair<VarId, VarId> def1 = varDefs.get(var1);
    int numShouldBeInverted = 0;
    int totalNum = 0;
    VarId var1_ = var1, var2_ = var2;

    while (def1 != null) {
      Pair<VarId, VarId> def2 = varDefs.get(var2_);
      var1_ = def1.proj1;
      var2_ = def2.proj1;
      if (shouldBeInverted(def1.proj2, def2.proj2)) {
        ++numShouldBeInverted;
      }
      if (!def1.proj2.equals(def2.proj2)) {
        ++totalNum;
      }
      def1 = varDefs.get(var1_);

    }

    if (shouldBeInverted(var1_, var2_)) {
      ++numShouldBeInverted;
    }

    if (!var1_.equals(var2_)) totalNum++;

    return 2 * numShouldBeInverted > totalNum;
  }

  private EqProofOrElement genCongrProof(VarId var1, VarId var2) {
    Pair<VarId, VarId> def1 = varDefs.get(var1);
    List<EqProofOrElement> eqProofs = new ArrayList<>();

    while (def1 != null) {
      Pair<VarId, VarId> def2 = varDefs.get(var2);
      var1 = def1.proj1;
      var2 = def2.proj1;
      eqProofs.add(checkEquality(def1.proj2, def2.proj2));
      def1 = varDefs.get(var1);
    }

    eqProofs.add(checkEquality(var1, var2));

    if (eqProofs.size() == 1) {
      return eqProofs.get(0);
    }

    Collections.reverse(eqProofs);
    return new EqProofOrElement(congrLemma.apply(eqProofs), false);
  }

  private void addToCongrTable(VarId var, Queue<Equality> pending) {
    List<VarId> congrList = congrTable.get(varHashCode(var));
    if (congrList == null) {
      congrTable.put(varHashCode(var), new ArrayList<>(Collections.singletonList(var)));
    } else {
      for (VarId congrDef : congrList) {
        if (areCongruent(var, congrDef, false)) {
          boolean shouldInvert = shouldInvertCongrProof(var, congrDef);
          EqProofOrElement proof = !shouldInvert ? genCongrProof(var, congrDef) : genCongrProof(congrDef, var);
          if (proof == null) continue;
          if (!shouldInvert) {
            pending.add(new Equality(var, congrDef, proof));
          } else {
            pending.add(new Equality(congrDef, var, proof));
          }
        }
      }
      congrList.add(var);
    }
  }

  private Set<VarId> getTransitiveOccurrences(VarId var) {
    Queue<VarId> toProcess = new ArrayDeque<>();
    Set<VarId> occurrences = new HashSet<>();

    toProcess.add(var);
    while (!toProcess.isEmpty()) {
      VarId v = toProcess.poll();
      List<VarId> occurList = occurrenceLists.get(v);
      if (occurList == null) continue;

      for (VarId u : occurList) {
        if (occurrences.add(u)) {
          toProcess.add(u);
        }
      }
    }

    return occurrences;
  }

  private void updateCongrTable(VarId var1, VarId var2, Queue<Equality> pending) {
    Set<VarId> occurList = getTransitiveOccurrences(var1);

    occurList.add(var1);
    for (VarId containingDef : occurList) {
      congrTable.get(varHashCode(containingDef)).remove(containingDef);
    }

    varsEquivClasses.union(var1, var2);

    for (VarId containingDef : occurList) {
      addToCongrTable(containingDef, pending);
    }
  }

  private static class Equality {
    public VarId var1;
    public VarId var2;
    EqProofOrElement proof;

    public Equality(VarId var1, VarId var2, EqProofOrElement proof) {
      this.var1 = var1;
      this.var2 = var2;
      this.proof = proof;
    }
  }

  private void addEqualities(Queue<Equality> eqProofs) {
    while (!eqProofs.isEmpty()) {
      Equality eq = eqProofs.poll();
      VarId v1 = eq.var1, v2 = eq.var2;
      EqProofOrElement pr = eq.proof;

      if (varsEquivClasses.find(v1).equals(varsEquivClasses.find(v2))) {
        continue;
      }

      equivalenceClosure.addRelation(v1, v2, pr.eqProofOrElement);

      VarId var1Rep = varsEquivClasses.find(v1);
      VarId var2Rep = varsEquivClasses.find(v2);
      VarId unionVar = varsEquivClasses.compare(var1Rep, var2Rep);

      if (var1Rep != unionVar) {
        updateCongrTable(var1Rep, var2Rep, eqProofs);
      } else {
        updateCongrTable(var2Rep, var1Rep, eqProofs);
      }
    }
  }

  @Override
  public void addRelation(V value1, V value2, ConcreteExpression proof) {
    int var1 = splitIntoSubterms(value1);
    int var2 = splitIntoSubterms(value2);
    addEqualities(new ArrayDeque<>(Collections.singletonList(new Equality(new VarId(var1, -1), new VarId(var2, -1), new EqProofOrElement(proof, false)))));
  }

  @Override
  public @Nullable ConcreteExpression checkRelation(V value1, V value2) {
    VarId var1 = new VarId(splitIntoSubterms(value1), -1);
    VarId var2 = new VarId(splitIntoSubterms(value2), -1);

    EqProofOrElement eqProof = checkEquality(var1, var2);
    if (eqProof.eqProofOrElement != null) {
      if (!eqProof.isElement) {
        return eqProof.eqProofOrElement;
      }
      ConcreteFactory factory = equivalenceClosure.factory;
      //return factory.app(equivalenceClosure.refl, Collections.singletonList(factory.arg(eqProof.eqProofOrElement, false)));
      return equivalenceClosure.refl;
    }

    if (congrTable.get(varHashCode(var1)).contains(var2)) {
      if (areCongruent(var1, var2, false)) {
        return genCongrProof(var1, var2).eqProofOrElement;
      }
    }

    return null;
  }

  private int varHashCode(VarId var) {
    Pair<VarId, VarId> def = varDefs.get(var);
    if (def != null) {
      VarId func = varsEquivClasses.find(def.proj1);
      VarId arg = varsEquivClasses.find(def.proj2);
      return Objects.hash(varHashCode(func), varHashCode(arg));
    }
    return Objects.hash(varsEquivClasses.find(var));
  }


  private static class VarId {
    public int value;
    public int prefix;

    public VarId(int value, int prefix) {
      this.value = value;
      this.prefix = prefix;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      VarId varId = (VarId) o;
      return value == varId.value &&
          prefix == varId.prefix;
    }

    @Override
    public int hashCode() {
      return Objects.hash(value, prefix);
    }
  }

  private static class ValuesEx extends Values<CoreExpression> {
    public ValuesEx(ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
      super(typechecker, marker);
    }

    public List<VarId> getVarIds(CoreExpression value) {
      int prefixSize = 0;
      List<VarId> result = new ArrayList<>();
      int index = getIndex(value);

      if (index == -1) {
        return result;
      }

      if (!(value instanceof CoreDefCallExpression)) {
        return result;
      }

      List<Integer> argInds = new ArrayList<>();

      for (CoreExpression arg : ((CoreDefCallExpression) value).getDefCallArguments()) {
        int argInd = getIndex(arg);
        argInds.add(argInd);
      }

      int numArgs = argInds.size();

      for (int i = 0; i < values.size(); i++) {
        if (i == index) continue;
        CoreExpression element = values.get(i);
        if (element instanceof CoreDefCallExpression && ((CoreDefCallExpression) value).getDefinition().equals(((CoreDefCallExpression) element).getDefinition())) {
          if (((CoreDefCallExpression) element).getDefCallArguments().size() != numArgs) return Collections.emptyList();
          if (prefixSize == 0) {
            result.add(new VarId(i, numArgs - prefixSize - 1));
            ++prefixSize;
          }
          for (int j = 0; j < numArgs; ++j) {
            if (argInds.get(j) == -1) {
              break;
            }
            int elementArg = getIndex(((CoreDefCallExpression) element).getDefCallArguments().get(j));
            if (argInds.get(j) == elementArg) {
              if (prefixSize <= j + 1) {
                result.add(new VarId(i, numArgs - prefixSize - 1));
                ++prefixSize;
              }
            } else {
              break;
            }
          }
          if (prefixSize > argInds.size() || prefixSize > 0 && argInds.get(prefixSize - 1) == -1) {
            break;
          }
        }
      }

      for (int i = 0; i < numArgs - prefixSize; ++i) {
        result.add(null);
      }

      result.add(new VarId(index, -1));
      Collections.reverse(result);

      return result;
    }

  } /**/

  interface DisjointSet<W> {
    W find(W x);

    void union(W x, W y);

    W compare(W x, W y);
  }

  private static class DisjointSetImpl<W> implements DisjointSet<W> {
    private final Map<W, W> parent = new HashMap<>();
    private final Map<W, Integer> size = new HashMap<>();

    @Override
    public W find(W w) {
      if (parent.get(w) == null) {
        parent.put(w, w);
        size.put(w, 1);
        return w;
      }
      W z = w;
      W p = parent.get(z);
      while (z != p) {
        W pp = parent.get(p);
        parent.remove(z);
        parent.put(z, pp);
        z = p;
        p = pp;
      }
      return z;
    }

    @Override
    public void union(W x, W y) {
      W xRep = find(x), yRep = find(y);
      if (xRep == yRep) return;

      W z = compare(xRep, yRep);
      if (z == xRep) {
        parent.put(yRep, xRep);
        size.put(xRep, size.get(xRep) + size.get(yRep));
        size.remove(yRep);
      } else {
        parent.put(xRep, yRep);
        size.put(yRep, size.get(xRep) + size.get(yRep));
        size.remove(xRep);
      }
    }

    @Override
    public W compare(W x, W y) {
      W xRep = find(x), yRep = find(y);
      if (size.get(xRep) > size.get(yRep)) {
        return x;
      }
      return y;
    }
  }
}
