package org.arend.lib.meta;

import org.arend.ext.RawDefinitionProvider;
import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFieldCallExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypeMismatchError;
import org.arend.ext.module.ModulePath;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.RawScope;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.CheckedExpression;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.lib.StdExtension;
import org.arend.lib.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class AlgebraSolverMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public CoreClassField carrier;
  public CoreClassField ide;
  public CoreClassField mul;

  private CoreConstructor varTerm;
  private CoreConstructor ideTerm;
  private CoreConstructor mulTerm;

  private CoreClassDefinition dataClass;
  private CoreFunctionDefinition termsEq;

  public AlgebraSolverMeta(StdExtension ext) {
    this.ext = ext;
  }

  public void load(RawDefinitionProvider provider) {
    carrier = provider.getDefinition(ext.moduleScopeProvider.forModule(new ModulePath("Set")).resolveName("BaseSet"), CoreClassDefinition.class).getPersonalFields().get(0);
    ide = provider.getDefinition(ext.moduleScopeProvider.forModule(ModulePath.fromString("Algebra.Pointed")).resolveName("Pointed"), CoreClassDefinition.class).getPersonalFields().get(0);

    mul = provider.getDefinition(ext.moduleScopeProvider.forModule(ModulePath.fromString("Algebra.Monoid")).resolveName("Monoid"), CoreClassDefinition.class).getPersonalFields().get(0);
    RawScope solverScope = ext.moduleScopeProvider.forModule(ModulePath.fromString("Algebra.Monoid.Solver"));
    CoreDataDefinition term = provider.getDefinition(solverScope.resolveName("MonoidTerm"), CoreDataDefinition.class);
    varTerm = term.getConstructors().get(0);
    ideTerm = term.getConstructors().get(1);
    mulTerm = term.getConstructors().get(2);
    dataClass = provider.getDefinition(solverScope.resolveName("Data"), CoreClassDefinition.class);
    RawScope dataScope = solverScope.getSubscope("Data");
    termsEq = provider.getDefinition(dataScope.resolveName("terms-equality"), CoreFunctionDefinition.class);
  }

  @Override
  protected @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false };
  }

  @Override
  protected boolean requireExpectedType() {
    return true;
  }

  @Override
  public @Nullable CheckedExpression invoke(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    CoreFunCallExpression equality = Utils.toEquality(contextData.getExpectedType(), errorReporter, refExpr);
    if (equality == null) {
      return null;
    }

    CoreExpression instance = null;
    CoreExpression type = equality.getDefCallArguments().get(0).normalize(NormalizationMode.WHNF).getUnderlyingExpression();
    if (type instanceof CoreFieldCallExpression) {
      if (((CoreFieldCallExpression) type).getDefinition() == carrier) {
        instance = ((CoreFieldCallExpression) type).getArgument();
      }
    }
    if (instance == null) {
      errorReporter.report(new TypeMismatchError(DocFactory.text("Expected an equality in a monoid"), equality, refExpr));
      return null;
    }

    List<CoreExpression> values = new ArrayList<>();
    List<Integer> nf1 = new ArrayList<>();
    List<Integer> nf2 = new ArrayList<>();
    ConcreteExpression term1 = computeTerm(equality.getDefCallArguments().get(1), values, typechecker, refExpr, factory, nf1);
    ConcreteExpression term2 = computeTerm(equality.getDefCallArguments().get(2), values, typechecker, refExpr, factory, nf2);

    ArendRef letClause = factory.local("d");
    ArendRef lamParam = factory.local("n");
    ConcreteClause[] caseClauses = new ConcreteClause[values.size() + 1];
    for (int i = 0; i < values.size(); i++) {
      caseClauses[i] = factory.clause(Collections.singletonList(factory.numberPattern(i)), factory.core("c" + i, typechecker.check(values.get(i), refExpr)));
    }
    caseClauses[values.size()] = factory.clause(Collections.singletonList(factory.refPattern(null, null)), factory.ref(ide.getRef()));

    return typechecker.typecheck(ext.factory.letExpr(false,
        Collections.singletonList(factory.letClause(letClause, Collections.emptyList(), null, factory.newExpr(factory.app(
            factory.ref(dataClass.getRef()), true,
            Collections.singletonList(factory.lam(Collections.singletonList(factory.param(Collections.singletonList(lamParam), factory.ref(ext.prelude.getNat().getRef()))),
                                                  factory.caseExpr(false, Collections.singletonList(factory.caseArg(factory.ref(lamParam), null, null)), null, null, caseClauses))))))),
        factory.app(factory.ref(termsEq.getRef()), Arrays.asList(factory.arg(factory.ref(letClause), false), factory.arg(term1, true), factory.arg(term2, true), factory.arg(factory.ref(ext.prelude.getIdp().getRef()), true)))), null);
  }

  private ConcreteExpression computeTerm(CoreExpression expression, List<CoreExpression> values, ExpressionTypechecker typechecker, ConcreteReferenceExpression marker, ConcreteFactory factory, List<Integer> nf) {
    expression = expression.normalize(NormalizationMode.WHNF).getUnderlyingExpression();
    if (expression instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) expression).getDefinition() == ide) {
      return factory.ref(ideTerm.getRef());
    }

    List<CoreExpression> args = new ArrayList<>(2);
    CoreExpression function = Utils.getAppArguments(expression, 2, args);
    if (args.size() == 2) {
      function = function.normalize(NormalizationMode.WHNF).getUnderlyingExpression();
      if (function instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) function).getDefinition() == mul) {
        List<ConcreteExpression> cArgs = new ArrayList<>(2);
        cArgs.add(computeTerm(args.get(0), values, typechecker, marker, factory, nf));
        cArgs.add(computeTerm(args.get(1), values, typechecker, marker, factory, nf));
        return factory.app(factory.ref(mulTerm.getRef()), true, cArgs);
      }
    }

    int index = values.size();
    for (int i = 0; i < values.size(); i++) {
      if (typechecker.compare(expression, values.get(i), CMP.EQ, marker, false, true)) {
        index = i;
        break;
      }
    }

    if (index == values.size()) {
      values.add(expression);
    }

    nf.add(index);
    return factory.app(factory.ref(varTerm.getRef()), true, Collections.singletonList(factory.number(index)));
  }
}
