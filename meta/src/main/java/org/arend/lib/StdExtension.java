package org.arend.lib;

import org.arend.ext.*;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreDataDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.module.LongName;
import org.arend.ext.module.ModulePath;
import org.arend.ext.module.ModuleScopeProvider;
import org.arend.ext.reference.Precedence;
import org.arend.ext.reference.RawScope;
import org.arend.ext.typechecking.*;
import org.arend.lib.meta.*;

import org.jetbrains.annotations.NotNull;

@SuppressWarnings("unused")
public class StdExtension implements ArendExtension {
  public ArendPrelude prelude;

  public ConcreteFactory factory;
  public ModuleScopeProvider moduleScopeProvider;
  public DefinitionProvider definitionProvider;

  public CoreFunctionDefinition transport;
  public CoreFunctionDefinition transportInv;
  public CoreFunctionDefinition concat;
  public CoreFunctionDefinition inv;

  public CoreConstructor nil;
  public CoreConstructor cons;

  public AlgebraSolverMeta algebraMeta = new AlgebraSolverMeta(this);

  @Override
  public void setPrelude(@NotNull ArendPrelude prelude) {
    this.prelude = prelude;
  }

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
  public void setDefinitionProvider(@NotNull DefinitionProvider definitionProvider) {
    this.definitionProvider = definitionProvider;
  }

  @Override
  public void load(@NotNull RawDefinitionProvider provider) {
    RawScope paths = moduleScopeProvider.forModule(new ModulePath("Paths"));
    transport = provider.getDefinition(paths.resolveName("transport"), CoreFunctionDefinition.class);
    transportInv = provider.getDefinition(paths.resolveName("transportInv"), CoreFunctionDefinition.class);
    concat = provider.getDefinition(paths.resolveName("*>"), CoreFunctionDefinition.class);
    inv = provider.getDefinition(paths.resolveName("inv"), CoreFunctionDefinition.class);

    CoreDataDefinition list = provider.getDefinition(moduleScopeProvider.forModule(ModulePath.fromString("Data.List")).resolveName("List"), CoreDataDefinition.class);
    nil = list.getConstructors().get(0);
    cons = list.getConstructors().get(1);

    algebraMeta.load(provider);
  }

  @Override
  public void declareDefinitions(DefinitionContributor contributor) {
    contributor.declare(new ModulePath("Meta"), new LongName("later"), "`later meta args` defers the invocation of `meta args`", Precedence.DEFAULT, new LaterMeta());

    ModulePath paths = ModulePath.fromString("Paths.Meta");
    contributor.declare(paths, new LongName("rewrite"),
        "`rewrite (p : a = b) : T` replaces occurrences of `a` in `T` with a variable `x` obtaining a type `T[x/a]` and returns `transport (\\lam x => T[x/a]) p`\n\n" +
        "`rewrite {i_1, ... i_k} p` replaces only occurrences with indices `i_1`, ... `i_k`\n" +
        "Also, `p` may be a reference to a definition with parameters, in which case `rewrite p` is equivalent to `rewrite (p _ ... _)`",
        Precedence.DEFAULT, new RewriteMeta(this, false, true));
    contributor.declare(paths, new LongName("rewriteI"),
        "`rewriteI p` is equivalent to `rewrite (inv p)`",
        Precedence.DEFAULT, new RewriteMeta(this, false, false));
    contributor.declare(paths, new LongName("rewriteF"),
        "`rewriteF (p : a = b) e` is similar to `rewrite`, but it replaces occurrences of `a` in the type of `e` instead of the expected type",
        Precedence.DEFAULT, new RewriteMeta(this, true, false));

    MetaDefinition apply = new ApplyMeta(this);
    ModulePath function = ModulePath.fromString("Function.Meta");
    contributor.declare(function, new LongName("$"), "`f $ a` returns `f a`", new Precedence(Precedence.Associativity.RIGHT_ASSOC, (byte) 0, true), apply);
    contributor.declare(function, new LongName("#"), "`f # a` returns `f a`", new Precedence(Precedence.Associativity.LEFT_ASSOC, (byte) 0, true), apply);
    contributor.declare(function, new LongName("repeat"),
        "`repeat {n} f x` returns `f^n(x)\n\n`" +
        "`repeat f x` repeats `f` until it fails and returns `x` in this case",
        Precedence.DEFAULT, new RepeatMeta(this));

    contributor.declare(new ModulePath("Algebra"), new LongName("solve"), "Proves equations in monoids", Precedence.DEFAULT, algebraMeta);
  }
}
