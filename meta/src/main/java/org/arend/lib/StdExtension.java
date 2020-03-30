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
    contributor.declare(ModulePath.fromString("Meta"), new LongName("later"), "`later meta args` defers the invocation of `meta args`", Precedence.DEFAULT, new LaterMeta());

    ModulePath paths = ModulePath.fromString("Paths.Meta");
    contributor.declare(paths, new LongName("rewrite"),
        "`rewrite (p : a = b) : T` replaces occurrences of `a` in `T` with a variable `x` obtaining a type `T[x/a]` and returns `transport (\\lam x => T[x/a]) p`\n\n" +
        "`rewrite {i_1, ... i_k} p` replaces only occurrences with indices `i_1`, ... `i_k`\n" +
        "Also, `p` may be a function with, in which case `rewrite p` is equivalent to `rewrite (p _ ... _)`",
        Precedence.DEFAULT, new RewriteMeta(this, false, true));
    contributor.declare(paths, new LongName("rewriteI"),
        "`rewriteI p` is equivalent to `rewrite (inv p)`",
        Precedence.DEFAULT, new RewriteMeta(this, false, false));
    contributor.declare(paths, new LongName("rewriteF"),
        "`rewriteF (p : a = b) e` is similar to `rewrite`, but it replaces occurrences of `a` in the type of `e` instead of the expected type",
        Precedence.DEFAULT, new RewriteMeta(this, true, false));

    MetaDefinition apply = new ApplyMeta();
    ModulePath function = ModulePath.fromString("Function.Meta");
    contributor.declare(function, new LongName("$"), "`f $ a` returns `f a`", new Precedence(Precedence.Associativity.RIGHT_ASSOC, (byte) 0, true), apply);
    contributor.declare(function, new LongName("#"), "`f # a` returns `f a`", new Precedence(Precedence.Associativity.LEFT_ASSOC, (byte) 0, true), apply);
  }
}
