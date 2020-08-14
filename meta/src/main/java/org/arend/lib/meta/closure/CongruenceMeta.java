package org.arend.lib.meta.closure;

import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.*;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.context.Context;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.util.Utils;
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

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false };
  }

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  private ConcreteExpression appAt(ExpressionTypechecker typechecker, CongruenceClosure.EqProofOrElement path, ArendRef param) {
    //ConcreteArgument atA = ext.factory.arg(ext.factory.lam(Collections.singleton(ext.factory.param(param)), ext.factory.core(path)), false);
    //CoreExpression element = elementFromIdp(path.getExpression());
    if (path.isElement) {
      return path.eqProofOrElement; //ext.factory.core(element.computeTyped());
    }
    // ConcreteExpression cpath = ext.factory.core(path);
    TypedExpression pathChecked = typechecker.typecheck(path.eqProofOrElement, null);
    CoreDefCallExpression equality = pathChecked != null ? pathChecked.getType().toEquality() : null;
    if (equality != null) {
      ArendRef iParam = ext.factory.local("i");
      ConcreteExpression funcLam = ext.factory.lam(Collections.singletonList(ext.factory.param(iParam)), ext.factory.core(equality.getDefCallArguments().get(0).computeTyped()));
      return ext.factory.app(ext.factory.ref(ext.prelude.getAt().getRef()), Arrays.asList(ext.factory.arg(funcLam, false), ext.factory.arg(path.eqProofOrElement, true), ext.factory.arg(ext.factory.ref(param), true)));
    }
    return ext.factory.app(ext.factory.ref(ext.prelude.getAt().getRef()), Arrays.asList(ext.factory.arg(path.eqProofOrElement, true), ext.factory.arg(ext.factory.ref(param), true)));
  }

  private ConcreteExpression applyCongruence(ExpressionTypechecker typechecker, List<CongruenceClosure.EqProofOrElement> eqProofs) {
    if (eqProofs.isEmpty()) return null;

    //TypedExpression funcProof = typechecker.typecheck(eqProofs.get(0), null);
    // if (funcProof == null)  return null;

    // CoreDefCallExpression funcEquality = funcProof.getType().toEquality();
    // if (funcEquality == null) return null;

    // CoreExpression funcType = funcEquality.getDefCallArguments().get(0);
    // if (!(funcType instanceof CorePiExpression)) return null;
    // funcType = ((CoreLamExpression) funcType).getBody();

    ArendRef jParam = ext.factory.local("j");
    List<ConcreteArgument> eqProofsAtJ = new ArrayList<>();

    for (int i = 1; i < eqProofs.size(); ++i) {
      //TypedExpression argProof = typechecker.typecheck(eqProofs.get(i), null);
      eqProofsAtJ.add(ext.factory.arg(appAt(typechecker, eqProofs.get(i), jParam), true));
    }

    ConcreteExpression congrLambda = ext.factory.lam(Collections.singleton(ext.factory.param(jParam)), ext.factory.app(appAt(typechecker, eqProofs.get(0), jParam), eqProofsAtJ));

    return ext.factory.appBuilder(ext.factory.ref(ext.prelude.getPathCon().getRef())).app(congrLambda).build();
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    CoreFunCallExpression expectedType = Utils.toEquality(contextData.getExpectedType(), typechecker.getErrorReporter(), refExpr);
    if (expectedType == null) {
      return null;
    }

    ContextHelper contextHelper = new ContextHelper(Context.TRIVIAL, contextData.getArguments().isEmpty() ? null : contextData.getArguments().get(0).getExpression());
    if (contextHelper.meta == null && !contextData.getArguments().isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Argument is ignored", contextData.getArguments().get(0).getExpression()));
    }

    CongruenceClosure<CoreExpression> congruenceClosure = new CongruenceClosure<>(typechecker, refExpr, eqProofs -> applyCongruence(typechecker, eqProofs),
        new CongruenceClosure.EqualityIsEquivProof(ext.factory.ref(ext.prelude.getIdp().getRef()), ext.factory.ref(ext.inv.getRef()), ext.factory.ref(ext.concat.getRef())), ext.factory);
    for (CoreBinding binding : contextHelper.getAllBindings(typechecker)) {
      CoreFunCallExpression equality = binding.getTypeExpr().toEquality();
      if (equality != null) {
        congruenceClosure.addRelation(equality.getDefCallArguments().get(1), equality.getDefCallArguments().get(2), ext.factory.ref(binding));
      }
    }

    CoreExpression leftEqArg = expectedType.getDefCallArguments().get(1);
    CoreExpression rightEqArg = expectedType.getDefCallArguments().get(2);

    ConcreteExpression goalProof = congruenceClosure.checkRelation(leftEqArg, rightEqArg);
    if (goalProof == null) return null;
    return typechecker.typecheck(goalProof, contextData.getExpectedType());
  }
}
