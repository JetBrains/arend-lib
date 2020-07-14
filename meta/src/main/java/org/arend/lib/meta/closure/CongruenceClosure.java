package org.arend.lib.meta.closure;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.expr.CoreAppExpression;
import org.arend.ext.core.expr.UncheckedExpression;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.lib.util.Pair;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;

public class CongruenceClosure<V extends UncheckedExpression> implements BinaryRelationClosure<V> {
    private final Values<UncheckedExpression> terms;

    private final DisjointSet<Integer> varsEquivClasses = new DisjointSetImpl<>();
    private final EquivalenceClosure<Integer> equivalenceClosure;
    private final Map<Integer, Pair<Integer, Integer>> varDefs = new HashMap<>();
    private final Map<Integer, List<Integer>> occurrenceLists = new HashMap<>();
    private final Map<Integer, List<Integer>> congrTable = new HashMap<>();

    private final Function<Integer, ConcreteExpression> congrLemma;
    private final ConcreteFactory factory;

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

    public CongruenceClosure(ExpressionTypechecker typechecker, ConcreteSourceNode marker, Function<Integer, ConcreteExpression> congrLemma, EqualityIsEquivProof equalityIsEquivLemma, ConcreteFactory factory) {
        this.congrLemma = congrLemma;
        this.factory = factory;
        this.terms = new Values<>(typechecker, marker);
        this.equivalenceClosure = new EquivalenceClosure<>(equalityIsEquivLemma.refl, equalityIsEquivLemma.sym, equalityIsEquivLemma.trans, factory);
    }

    private void initAppExprVar(int var, int parentVar) {
        List<Integer> occurList = occurrenceLists.get(var);
        if (occurList == null) {
            occurList = Collections.singletonList(parentVar);
            occurrenceLists.put(var, occurList);
        } else { occurList.add(parentVar); }
    }

    private Integer splitIntoSubterms(V term) {
        Queue<Pair<UncheckedExpression, Integer>> termsToSplit = new ArrayDeque<>();
        List<Integer> toBeAddedToCongrTable = new ArrayList<>();

        int numOfTerms = terms.getValues().size();
        int inputTermVar = terms.addValue(term);

        if (numOfTerms == terms.getValues().size()) return inputTermVar;
        ++ numOfTerms;
        termsToSplit.add(new Pair<>(term, inputTermVar));

        while (!termsToSplit.isEmpty()) {
            Pair<UncheckedExpression, Integer> subtermPair = termsToSplit.poll();
            UncheckedExpression subterm = subtermPair.proj1;
            int var = subtermPair.proj2;

            toBeAddedToCongrTable.add(var);
            if (subterm instanceof CoreAppExpression) {
                UncheckedExpression func = ((CoreAppExpression) subterm).getFunction();
                UncheckedExpression arg = ((CoreAppExpression) subterm).getArgument();

                int funcVar = terms.addValue(func);
                if (numOfTerms != terms.getValues().size()) {
                    termsToSplit.add(new Pair<>(func, funcVar));
                    initAppExprVar(funcVar, var);
                    ++numOfTerms;
                }

                int argVar = terms.addValue(arg);
                if (numOfTerms != terms.getValues().size()) {
                    termsToSplit.add(new Pair<>(arg, argVar));
                    initAppExprVar(argVar, var);
                    ++numOfTerms;
                }

                varDefs.put(var, new Pair<>(funcVar, argVar));
            }
        }

        for (int var : toBeAddedToCongrTable) {
            List<Integer> congrList = congrTable.get(varHashCode(var));
            if (congrList == null) {
                congrTable.put(varHashCode(var), Collections.singletonList(var));
            } else {
                congrList.add(var);
            }
        }

        return inputTermVar;
    }

    private boolean areCongruent(int var1, int var2) {
        Pair<Integer, Integer> def1 = varDefs.get(var1);
        Pair<Integer, Integer> def2 = varDefs.get(var2);

        if ((def1 == null) != (def2 == null)) return false;

        if (def1 == null) return varsEquivClasses.find(var1).equals(varsEquivClasses.find(var2));

        return varsEquivClasses.find(def1.proj2).equals(varsEquivClasses.find(def2.proj2)) &&
                areCongruent(def1.proj1, def2.proj1);
    }

    private ConcreteExpression genCongrProof(int var1, int var2) {
        Pair<Integer, Integer> def1 = varDefs.get(var1);
        List<ConcreteExpression> eqProofs = new ArrayList<>();

        while (def1 != null) {
            Pair<Integer, Integer> def2 = varDefs.get(var2);
            var1 = def1.proj1; var2 = def2.proj1;
            eqProofs.add(equivalenceClosure.checkRelation(def1.proj2, def2.proj2));
            def1 = varDefs.get(var1);
        }

        eqProofs.add(equivalenceClosure.checkRelation(var1, var2));
        return factory.app(congrLemma.apply(eqProofs.size() - 1), true, eqProofs);
    }

    private void updateCongrTable(int var1, int var2, Queue<Equality> pending) {
        List<Integer> occurList = occurrenceLists.get(var1);
        if (occurList == null) return;

        for (int containingDef : occurList) {
            congrTable.get(varHashCode(containingDef)).remove(containingDef);
        }

        varsEquivClasses.union(var1, var2);

        for (int containingDef : occurList) {
            List<Integer> congrList = congrTable.get(varHashCode(containingDef));
            if (congrList == null) {
                congrTable.put(varHashCode(containingDef), Collections.singletonList(containingDef));
            } else {
                for (int congrDef : congrList) {
                    if (areCongruent(containingDef, congrDef)) {
                        pending.add(new Equality(containingDef, congrDef, genCongrProof(containingDef, congrDef)));
                    }
                }
                congrList.add(containingDef);
            }
        }
    }

    private static class Equality {
        public int var1;
        public int var2;
        ConcreteExpression proof;

        public Equality(int var1, int var2, ConcreteExpression proof) {
            this.var1 = var1;
            this.var2 = var2;
            this.proof = proof;
        }
    }

    private void addVarsEquality(int var1, int var2, ConcreteExpression proof) {
        Queue<Equality> pending = new ArrayDeque<>();
        pending.add(new Equality(var1, var2, proof));

        while (!pending.isEmpty()) {
            Equality eq = pending.poll();
            int v1 = eq.var1,  v2 = eq.var2;
            ConcreteExpression pr = eq.proof;

            equivalenceClosure.addRelation(v1, v2, pr);

            int var1Rep = varsEquivClasses.find(var1);
            int var2Rep = varsEquivClasses.find(var2);
            int unionVar = varsEquivClasses.compare(var1Rep, var2Rep);

            if (var1Rep == unionVar) {
                updateCongrTable(var1Rep, var2Rep, pending);
            } else {
                updateCongrTable(var2Rep, var1Rep, pending);
            }
        }
    }

    @Override
    public void addRelation(V value1, V value2, ConcreteExpression proof) {
        int var1 = splitIntoSubterms(value1);
        int var2 = splitIntoSubterms(value2);
        addVarsEquality(var1, var2, proof);
    }

    @Override
    public @Nullable ConcreteExpression checkRelation(V value1, V value2) {
        int var1 = splitIntoSubterms(value1);
        int var2 = splitIntoSubterms(value2);
        return equivalenceClosure.checkRelation(var1, var2);
    }

    private int varHashCode(int var) {
        Pair<Integer, Integer> def = varDefs.get(var);
        if (def != null) {
            int func = def.proj1;
            int arg = def.proj2;
            return Objects.hash(varHashCode(func), varHashCode(arg));
        }
        return Objects.hash(var);
    }

    interface DisjointSet<W> {
        W find(W x);
        void union(W x, W y);
        W compare(W x, W y);
       // void makeSet(W x);
    }

    private static class DisjointSetImpl<W> implements DisjointSet<W> {
        private final Map<W, W> parent = new HashMap<>();
        private final Map<W, Integer> size = new HashMap<>();

        @Override
        public W find(W x) {
            if (parent.get(x) == null) {
                parent.put(x, x);
                size.put(x, 1);
                return x;
            }
            W z = x;
            W p = parent.get(z);
            while (z != p) {
                W pp = parent.get(p);
                parent.remove(z);
                parent.put(z, pp);
                z = p; p = pp;
            }
            return z;
        }

        @Override
        public void union(W x, W y) {
            W xRep = find(x), yRep = find(y);
            if (size.get(xRep) > size.get(yRep)) {
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
