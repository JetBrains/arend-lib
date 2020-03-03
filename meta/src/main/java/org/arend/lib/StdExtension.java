package org.arend.lib;

import org.arend.ext.ArendExtension;
import org.arend.ext.DefinitionContributor;
import org.arend.ext.DefinitionProvider;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.module.LongName;
import org.arend.ext.module.ModulePath;
import org.arend.ext.module.ModuleScopeProvider;
import org.arend.ext.reference.Precedence;
import org.arend.ext.typechecking.*;
import org.arend.lib.tactic.RewriteTactic;

import org.jetbrains.annotations.NotNull;

@SuppressWarnings("unused")
public class StdExtension implements ArendExtension {
  public ConcreteFactory factory;
  public ModuleScopeProvider moduleScopeProvider;

  public CoreFunctionDefinition transport;

  @Override
  public void setConcreteFactory(@NotNull ConcreteFactory factory) {
    this.factory = factory;
  }

  @Override
  public void setModuleScopeProvider(@NotNull ModuleScopeProvider moduleScopeProvider) {
    this.moduleScopeProvider = moduleScopeProvider;
  }

  @NotNull
  @Override
  public ModuleScopeProvider getModuleScopeProvider() {
    return moduleScopeProvider;
  }

  @Override
  public void load(@NotNull DefinitionProvider provider) {
    transport = provider.getDefinition(moduleScopeProvider.forModule(new ModulePath("Paths")).resolveName("transport"), CoreFunctionDefinition.class);
  }

  @Override
  public void declareDefinitions(DefinitionContributor contributor) {
    MetaDefinition meta = new RewriteTactic(this);
    contributor.declare(ModulePath.fromString("Paths.Meta"), LongName.fromString("rewrite"), Precedence.DEFAULT, new DeferredMetaDefinition(ExpressionTypechecker.Stage.AFTER_LEVELS, meta));
    contributor.declare(ModulePath.fromString("Paths.Meta"), LongName.fromString("rewrite1"), Precedence.DEFAULT, new DeferredMetaDefinition(ExpressionTypechecker.Stage.BEFORE_SOLVER, meta));
    contributor.declare(ModulePath.fromString("Paths.Meta"), LongName.fromString("rewrite2"), Precedence.DEFAULT, new DeferredMetaDefinition(ExpressionTypechecker.Stage.BEFORE_LEVELS, meta));
    contributor.declare(ModulePath.fromString("Paths.Meta"), LongName.fromString("rewrite3"), Precedence.DEFAULT, new DeferredMetaDefinition(ExpressionTypechecker.Stage.AFTER_LEVELS, meta));
  }
}
