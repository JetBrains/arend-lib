package org.arend.lib;

import org.arend.ext.ArendExtension;
import org.arend.ext.DefinitionContributor;
import org.arend.ext.DefinitionProvider;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.error.TypeMismatchError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.module.LongName;
import org.arend.ext.module.ModulePath;
import org.arend.ext.module.ModuleScopeProvider;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.Precedence;
import org.arend.ext.typechecking.*;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Collections;

@SuppressWarnings("unused")
public class StdExtension implements ArendExtension {
  private ConcreteFactory factory;
  private ModuleScopeProvider moduleScopeProvider;

  private CoreFunctionDefinition transport;

  @Override
  public void setConcreteFactory(@Nonnull ConcreteFactory factory) {
    this.factory = factory;
  }

  @Override
  public void setModuleScopeProvider(@Nonnull ModuleScopeProvider moduleScopeProvider) {
    this.moduleScopeProvider = moduleScopeProvider;
  }

  @Nonnull
  @Override
  public ModuleScopeProvider getModuleScopeProvider() {
    return moduleScopeProvider;
  }

  @Override
  public void load(@Nonnull DefinitionProvider provider) {
    transport = provider.getDefinition(moduleScopeProvider.forModule(new ModulePath("Paths")).resolveName("transport"), CoreFunctionDefinition.class);
  }

  @Override
  public void declareDefinitions(DefinitionContributor contributor) {
    contributor.declare(ModulePath.fromString("Paths.Meta"), LongName.fromString("rewrite"), Precedence.DEFAULT, new DeferredMetaDefinition(new BaseMetaDefinition() {
      @Override
      protected boolean[] argumentExplicitness() {
        return new boolean[] { true, true };
      }

      @Override
      public CheckedExpression invoke(@Nonnull ExpressionTypechecker typechecker, @Nonnull ContextData contextData) {
        ConcreteExpression arg0 = contextData.getArguments().get(0).getExpression();
        CheckedExpression path = typechecker.typecheck(arg0);
        if (path == null) {
          return null;
        }
        CoreFunCallExpression eq = path.getType().toEquality();
        if (eq == null) {
          typechecker.getErrorReporter().report(new TypeMismatchError(DocFactory.text("_ = _"), path.getType(), arg0));
          return null;
        }

        CoreExpression right = eq.getDefCallArguments().get(2);
        CoreExpression type = contextData.getExpectedType();
        ConcreteExpression refExpr = contextData.getReferenceExpression();
        factory.withData(refExpr.getData());
        ArendRef ref = factory.local("x");
        return typechecker.typecheck(
          factory.ref(transport.getRef())
            .app(factory.lam(Collections.singletonList(factory.param(ref)), factory.meta("transport (\\lam x => {!}) _ _", new MetaDefinition() {
              @Nullable
              @Override
              public CheckedExpression invoke(@Nonnull ExpressionTypechecker typechecker, @Nonnull ContextData contextData) {
                CheckedExpression var = typechecker.typecheck(factory.ref(ref));
                assert var != null;
                CoreExpression absExpr = type.recreate(expression ->
                  typechecker.compare(expression, right, CMP.EQ, refExpr) ? var.getExpression() : null);
                if (absExpr == null) {
                  typechecker.getErrorReporter().report(new TypecheckingError("Cannot substitute expression", contextData.getReferenceExpression()));
                  return null;
                }
                return typechecker.check(absExpr);
              }
            })))
            .app(factory.core("transport _ {!} _", path))
            .app(contextData.getArguments().get(1).getExpression()));
      }
    }));
  }
}
