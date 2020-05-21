package org.arend.lib;

import org.arend.ext.*;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.dependency.ArendDependencyLoader;
import org.arend.ext.dependency.ArendDependencyProvider;
import org.arend.ext.module.LongName;
import org.arend.ext.module.ModulePath;
import org.arend.ext.reference.Precedence;
import org.arend.ext.typechecking.*;
import org.arend.ext.ui.ArendUI;
import org.arend.ext.variable.VariableRenamerFactory;
import org.arend.lib.goal.StdGoalSolver;
import org.arend.lib.meta.*;

import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

@SuppressWarnings("unused")
public class StdExtension implements ArendExtension {
  public ArendPrelude prelude;

  public ConcreteFactory factory;
  public DefinitionProvider definitionProvider;
  public VariableRenamerFactory renamerFactory;

  @Dependency(module = "Paths")              public CoreFunctionDefinition transport;
  @Dependency(module = "Paths")              public CoreFunctionDefinition transportInv;
  @Dependency(module = "Paths", name = "*>") public CoreFunctionDefinition concat;
  @Dependency(module = "Paths")              public CoreFunctionDefinition inv;

  @Dependency(module = "Data.List", name = "List.nil") public CoreConstructor nil;
  @Dependency(module = "Data.List", name = "List.::")  public CoreConstructor cons;

  public AlgebraSolverMeta algebraMeta = new AlgebraSolverMeta(this);

  private final StdGoalSolver goalSolver = new StdGoalSolver(this);

  public ArendUI ui;

  @Override
  public void setUI(@NotNull ArendUI ui) {
    this.ui = ui;
  }

  @Override
  public void setPrelude(@NotNull ArendPrelude prelude) {
    this.prelude = prelude;
  }

  @Override
  public void setConcreteFactory(@NotNull ConcreteFactory factory) {
    this.factory = factory;
  }

  @Override
  public void setDefinitionProvider(@NotNull DefinitionProvider definitionProvider) {
    this.definitionProvider = definitionProvider;
  }

  @Override
  public void setVariableRenamerFactory(@NotNull VariableRenamerFactory factory) {
    renamerFactory = factory;
  }

  @Override
  public void load(@NotNull ArendDependencyProvider provider) {
    ArendDependencyLoader.load(this, provider);
    ArendDependencyLoader.load(algebraMeta, provider);
  }

  @Override
  public void declareDefinitions(DefinitionContributor contributor) {
    ModulePath meta = new ModulePath("Meta");
    contributor.declare(meta, new LongName("later"), "`later meta args` defers the invocation of `meta args`", Precedence.DEFAULT, new LaterMeta());
    contributor.declare(meta, new LongName("fail"),
        "`fail meta args` succeeds if and only if `meta args` fails\n\n" +
        "`fail {T} meta args` succeeds if and only if `meta args : T` fails",
        Precedence.DEFAULT, new FailMeta(this));
    contributor.declare(meta, new LongName("using"),
        "`using (e_1, ... e_n) e` adds `e_1`, ... `e_n` to the context before checking `e`",
        Precedence.DEFAULT, new UsingMeta());
    contributor.declare(meta, new LongName("hiding"),
        "`hiding (x_1, ... x_n) e` hides local variables `x_1`, ... `x_n` from the context before checking `e`",
        Precedence.DEFAULT, new HidingMeta());

    ModulePath paths = ModulePath.fromString("Paths.Meta");
    contributor.declare(paths, new LongName("rewrite"),
        "`rewrite (p : a = b) : T` replaces occurrences of `a` in `T` with a variable `x` obtaining a type `T[x/a]` and returns `transport (\\lam x => T[x/a]) p`\n\n" +
        "`rewrite {i_1, ... i_k} p` replaces only occurrences with indices `i_1`, ... `i_k`\n" +
        "Also, `p` may be a function, in which case `rewrite p` is equivalent to `rewrite (p _ ... _)`",
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

    ModulePath algebra = ModulePath.fromString("Algebra.Meta");
    contributor.declare(algebra, new LongName("solve"), "Proves equations in monoids", Precedence.DEFAULT, new DeferredMetaDefinition(algebraMeta));
    contributor.declare(algebra, new LongName("equation"),
        "Proves equations\n\n" +
        "`equation a_1 ... a_n` proves an equation a_0 = a_{n+1} using a_1, ... a_n as intermediate steps\n" +
        "A proof of a_i = a_{i+1} can be specified as implicit arguments between them",
        Precedence.DEFAULT, new DeferredMetaDefinition(new EquationMeta(this), true));
  }

  @Override
  public @Nullable StdGoalSolver getGoalSolver() {
    return goalSolver;
  }
}
