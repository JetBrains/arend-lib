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
import org.arend.ext.reference.RawScope;
import org.arend.ext.typechecking.*;
import org.arend.lib.meta.ApplyMeta;
import org.arend.lib.meta.LaterMeta;
import org.arend.lib.meta.RewriteMeta;

import org.jetbrains.annotations.NotNull;

@SuppressWarnings("unused")
public class StdExtension implements ArendExtension {
  public ConcreteFactory factory;
  public ModuleScopeProvider moduleScopeProvider;

  public CoreFunctionDefinition transport;
  public CoreFunctionDefinition transportInv;

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
    RawScope scope = moduleScopeProvider.forModule(new ModulePath("Paths"));
    transport = provider.getDefinition(scope.resolveName("transport"), CoreFunctionDefinition.class);
    transportInv = provider.getDefinition(scope.resolveName("transportInv"), CoreFunctionDefinition.class);
  }

  @Override
  public void declareDefinitions(DefinitionContributor contributor) {
    contributor.declare(ModulePath.fromString("Meta"), new LongName("later"), Precedence.DEFAULT, new LaterMeta());

    ModulePath paths = ModulePath.fromString("Paths.Meta");
    contributor.declare(paths, new LongName("rewrite"), Precedence.DEFAULT, new RewriteMeta(this));
    contributor.declare(paths, new LongName("rewriteF"), Precedence.DEFAULT, new RewriteMeta(this, true));

    MetaDefinition apply = new ApplyMeta();
    ModulePath function = ModulePath.fromString("Function.Meta");
    contributor.declare(function, new LongName("$"), new Precedence(Precedence.Associativity.RIGHT_ASSOC, (byte) 0, true), apply);
    contributor.declare(function, new LongName("#"), new Precedence(Precedence.Associativity.LEFT_ASSOC, (byte) 0, true), apply);
  }
}
