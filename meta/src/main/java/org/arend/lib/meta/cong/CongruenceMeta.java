package org.arend.lib.meta.cong;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.*;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.context.Context;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.meta.closure.CongruenceClosure;
import org.arend.lib.util.Pair;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class CongruenceMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public CongruenceMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  private ConcreteExpression appAt(ExpressionTypechecker typechecker, CongruenceClosure.EqProofOrElement path, ArendRef param, ConcreteFactory factory) {
    if (path.isElement) {
      return path.eqProofOrElement;
    }
    TypedExpression pathChecked = typechecker.typecheck(path.eqProofOrElement, null);
    CoreDefCallExpression equality = pathChecked != null ? pathChecked.getType().toEquality() : null;
    if (equality != null) {
      ArendRef iParam = factory.local("i");
      ConcreteExpression funcLam = factory.lam(Collections.singletonList(factory.param(iParam)), factory.core(equality.getDefCallArguments().get(0).computeTyped()));
      return factory.app(factory.ref(ext.prelude.getAt().getRef()), Arrays.asList(factory.arg(funcLam, false), factory.arg(path.eqProofOrElement, true), factory.arg(factory.ref(param), true)));
    }
    return factory.app(factory.ref(ext.prelude.getAt().getRef()), Arrays.asList(factory.arg(path.eqProofOrElement, true), factory.arg(factory.ref(param), true)));
  }

  private ConcreteExpression applyCongruence(ExpressionTypechecker typechecker, List<CongruenceClosure.EqProofOrElement> eqProofs, ConcreteFactory factory) {
    if (eqProofs.isEmpty()) return null;

    ArendRef jParam = factory.local("j");
    List<ConcreteArgument> eqProofsAtJ = new ArrayList<>();

    for (int i = 1; i < eqProofs.size(); ++i) {
      eqProofsAtJ.add(factory.arg(appAt(typechecker, eqProofs.get(i), jParam, factory), true));
    }

    ConcreteExpression congrLambda = factory.lam(Collections.singleton(factory.param(jParam)), factory.app(appAt(typechecker, eqProofs.get(0), jParam, factory), eqProofsAtJ));

    return factory.appBuilder(factory.ref(ext.prelude.getPathCon().getRef())).app(congrLambda).build();
  }

  private TypedExpression mapMode(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    CoreExpression equality = contextData.getExpectedType().normalize(NormalizationMode.WHNF);
    if (!(equality instanceof CoreDataCallExpression && ((CoreDataCallExpression) equality).getDefinition() == ext.prelude.getPath())) {
      return null;
    }

    List<? extends CoreExpression> args = ((CoreDataCallExpression) equality).getDefCallArguments();
    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    ArendRef iRef = factory.local("i");
    CongVisitor visitor = new CongVisitor(ext.prelude, factory, typechecker, contextData.getMarker(), contextData.getArguments().stream().map(ConcreteArgument::getExpression).collect(Collectors.toList()), iRef);
    ConcreteExpression result = args.get(1).accept(visitor, new Pair<>(() -> factory.core(args.get(0).computeTyped()), args.get(2)));
    if (result == null) {
      typechecker.getErrorReporter().report(new MissingArgumentsError(visitor.index - contextData.getArguments().size(), contextData.getMarker()));
      return null;
    }

    return typechecker.typecheck(factory.app(factory.ref(ext.prelude.getPathCon().getRef()), true, Collections.singletonList(factory.lam(Collections.singletonList(factory.param(iRef)), result))), contextData.getExpectedType());
  }

  @Override
  public boolean checkContextData(@NotNull ContextData contextData, @NotNull ErrorReporter errorReporter) {
    if (!contextData.getArguments().isEmpty() && contextData.getArguments().get(0).isExplicit()) {
      for (ConcreteArgument argument : contextData.getArguments()) {
        if (!argument.isExplicit()) {
          errorReporter.report(new ArgumentExplicitnessError(true, argument.getExpression()));
          return false;
        }
      }
    } else if (contextData.getArguments().size() > 1) {
      errorReporter.report(new TypecheckingError("Too many arguments", contextData.getArguments().get(1).getExpression()));
      return false;
    }
    return super.checkContextData(contextData, errorReporter);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    if (!contextData.getArguments().isEmpty() && contextData.getArguments().get(0).isExplicit()) {
      return mapMode(typechecker, contextData);
    }

    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    CoreFunCallExpression expectedType = Utils.toEquality(contextData.getExpectedType(), typechecker.getErrorReporter(), refExpr);
    if (expectedType == null) {
      return null;
    }

    ContextHelper contextHelper = new ContextHelper(Context.TRIVIAL, contextData.getArguments().isEmpty() ? null : contextData.getArguments().get(0).getExpression());
    if (contextHelper.meta == null && !contextData.getArguments().isEmpty()) {
      typechecker.getErrorReporter().report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Argument is ignored", contextData.getArguments().get(0).getExpression()));
    }

    ConcreteFactory factory = ext.factory.withData(refExpr);
    CongruenceClosure<CoreExpression> congruenceClosure = new CongruenceClosure<>(typechecker, refExpr, eqProofs -> applyCongruence(typechecker, eqProofs, factory),
        new CongruenceClosure.EqualityIsEquivProof(factory.ref(ext.prelude.getIdp().getRef()), factory.ref(ext.inv.getRef()), factory.ref(ext.concat.getRef())), factory);
    for (CoreBinding binding : contextHelper.getAllBindings(typechecker)) {
      CoreFunCallExpression equality = binding.getTypeExpr().toEquality();
      if (equality != null) {
        congruenceClosure.addRelation(equality.getDefCallArguments().get(1), equality.getDefCallArguments().get(2), factory.ref(binding));
      }
    }

    CoreExpression leftEqArg = expectedType.getDefCallArguments().get(1);
    CoreExpression rightEqArg = expectedType.getDefCallArguments().get(2);

    ConcreteExpression goalProof = congruenceClosure.checkRelation(leftEqArg, rightEqArg);
    if (goalProof == null) return null;

    return typechecker.typecheck(goalProof, contextData.getExpectedType());
  }
}
