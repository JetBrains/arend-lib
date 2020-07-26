package org.arend.lib.meta.equation;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreDefCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.expr.CoreLamExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.closure.CongruenceClosure;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class CongruenceMeta extends BaseMetaDefinition {
    private final StdExtension ext;

    public CongruenceMeta(StdExtension ext) {
        this.ext = ext;
    }

    private ConcreteExpression appAt(ConcreteExpression path, ArendRef param) {
        return ext.factory.app(ext.factory.ref(ext.prelude.getAt().getRef()), Arrays.asList(ext.factory.arg(path, true), ext.factory.arg(ext.factory.ref(param), true)));
    }

    private ConcreteExpression applyCongruence(ExpressionTypechecker typechecker, List<ConcreteExpression> eqProofs) {
        if (eqProofs.isEmpty()) return null;

        TypedExpression funcProof = typechecker.typecheck(eqProofs.get(0), null);
        if (funcProof == null)  return null;

        CoreDefCallExpression funcEquality = funcProof.getType().toEquality();
        if (funcEquality == null) return null;

        CoreExpression funcType = funcEquality.getDefCallArguments().get(0);
        if (!(funcType instanceof CoreLamExpression)) return null;
       // funcType = ((CoreLamExpression) funcType).getBody();

        ArendRef jParam = ext.factory.local("j");
        List<ConcreteArgument> eqProofsAtJ = new ArrayList<>();

        for (int i = 1; i < eqProofs.size(); ++i) {
            eqProofsAtJ.add(ext.factory.arg(appAt(eqProofs.get(i), jParam), true));
        }

        ConcreteExpression congrLambda = ext.factory.lam(Collections.singleton(ext.factory.param(jParam)), ext.factory.app(appAt(eqProofs.get(0), jParam), eqProofsAtJ));

        return ext.factory.appBuilder(ext.factory.ref(ext.prelude.getPathCon().getRef())).app(congrLambda).build();
    }

    @Override
    public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
        CongruenceClosure<CoreExpression> congruenceClosure = new CongruenceClosure<>(typechecker, refExpr, eqProofs -> applyCongruence(typechecker, eqProofs),
                new CongruenceClosure.EqualityIsEquivProof(ext.factory.ref(ext.prelude.getIdp().getRef()), ext.factory.ref(ext.inv.getRef()), ext.factory.ref(ext.concat.getRef())), ext.factory);

        for (ConcreteArgument argument : contextData.getArguments()) {
            TypedExpression eqProof = typechecker.typecheck(argument.getExpression(), null);
            if (eqProof == null) return null;

            CoreFunCallExpression equality = eqProof.getType().toEquality();
            if (equality == null) return null;

            CoreExpression leftEqArg = equality.getDefCallArguments().get(1);
            CoreExpression rightEqArg = equality.getDefCallArguments().get(2);

            congruenceClosure.addRelation(leftEqArg, rightEqArg, ext.factory.core(eqProof));
        }

        CoreFunCallExpression expectedType = contextData.getExpectedType().toEquality();
        if (expectedType == null) return null;

        CoreExpression leftEqArg = expectedType.getDefCallArguments().get(1);
        CoreExpression rightEqArg = expectedType.getDefCallArguments().get(2);

        ConcreteExpression goalProof = congruenceClosure.checkRelation(leftEqArg,rightEqArg);
        if (goalProof == null) return null;
        return typechecker.typecheck(goalProof, contextData.getExpectedType());
    }
}
