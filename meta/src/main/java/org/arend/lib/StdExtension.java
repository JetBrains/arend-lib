package org.arend.lib;

import org.arend.ext.*;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreDataDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.dependency.ArendDependencyProvider;
import org.arend.ext.module.LongName;
import org.arend.ext.module.ModulePath;
import org.arend.ext.reference.Precedence;
import org.arend.ext.typechecking.*;
import org.arend.ext.ui.ArendUI;
import org.arend.ext.variable.VariableRenamerFactory;
import org.arend.lib.goal.StdGoalSolver;
import org.arend.lib.key.IrreflexivityKey;
import org.arend.lib.key.ReflexivityKey;
import org.arend.lib.key.TransitivityKey;
import org.arend.lib.level.StdLevelProver;
import org.arend.lib.meta.*;
import org.arend.lib.meta.closure.CongruenceMeta;
import org.arend.lib.meta.debug.PrintMeta;
import org.arend.lib.meta.debug.RandomMeta;
import org.arend.lib.meta.debug.TimeMeta;
import org.arend.lib.meta.equation.EquationMeta;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

@SuppressWarnings("unused")
public class StdExtension implements ArendExtension {
  public ArendPrelude prelude;

  public ConcreteFactory factory;
  public DefinitionProvider definitionProvider;
  public VariableRenamerFactory renamerFactory;

  public final IrreflexivityKey irreflexivityKey = new IrreflexivityKey("irreflexivity", this);
  public final TransitivityKey transitivityKey = new TransitivityKey("transitivity", this);
  public final ReflexivityKey reflexivityKey = new ReflexivityKey("reflexivity", this);

  @Dependency(module = "Paths")              public CoreFunctionDefinition transport;
  @Dependency(module = "Paths")              public CoreFunctionDefinition transportInv;
  @Dependency(module = "Paths", name = "*>") public CoreFunctionDefinition concat;
  @Dependency(module = "Paths")              public CoreFunctionDefinition inv;

  @Dependency(module = "Data.List", name = "List.nil") public CoreConstructor nil;
  @Dependency(module = "Data.List", name = "List.::")  public CoreConstructor cons;

  @Dependency(module = "Logic") public CoreDataDefinition Empty;
  @Dependency(module = "Logic") public CoreDataDefinition TruncP;

  public EquationMeta equationMeta = new EquationMeta(this);
  public ContradictionMeta contradictionMeta = new ContradictionMeta(this);

  private final StdGoalSolver goalSolver = new StdGoalSolver(this);
  private final StdLevelProver levelProver = new StdLevelProver(this);
  private final StdNumberTypechecker numberTypechecker = new StdNumberTypechecker(this);
  private final ListDefinitionListener definitionListener = new ListDefinitionListener().addDeclaredListeners(this);
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
    provider.load(this);
    provider.load(equationMeta);
  }

  @Override
  public void declareDefinitions(@NotNull DefinitionContributor contributor) {
    ModulePath meta = new ModulePath("Meta");
    contributor.declare(meta, new LongName("later"), "`later meta args` defers the invocation of `meta args`", Precedence.DEFAULT, new LaterMeta());
    contributor.declare(meta, new LongName("fails"),
        "`fails meta args` succeeds if and only if `meta args` fails\n\n" +
        "`fails {T} meta args` succeeds if and only if `meta args : T` fails",
        Precedence.DEFAULT, new FailsMeta(this));
    contributor.declare(meta, new LongName("using"),
        "`using (e_1, ... e_n) e` adds `e_1`, ... `e_n` to the context before checking `e`",
        Precedence.DEFAULT, new UsingMeta(true));
    contributor.declare(meta, new LongName("usingOnly"),
        "`usingOnly (e_1, ... e_n) e` replaces the context with `e_1`, ... `e_n` before checking `e`",
        Precedence.DEFAULT, new UsingMeta(false));
    contributor.declare(meta, new LongName("hiding"),
        "`hiding (x_1, ... x_n) e` hides local variables `x_1`, ... `x_n` from the context before checking `e`",
        Precedence.DEFAULT, new HidingMeta());
    contributor.declare(meta, new LongName("run"), "`run { e_1, ... e_n }` is equivalent to `e_1 $ e_2 $ ... $ e_n`", Precedence.DEFAULT, new RunMeta(this));
    contributor.declare(meta, new LongName("at"), "`(f at x) r` replaces variable `x` with `f x` and runs `r` in the modified context", new Precedence(Precedence.Associativity.NON_ASSOC, (byte) 1, true), new AtMeta(this));

    ModulePath paths = ModulePath.fromString("Paths.Meta");
    contributor.declare(paths, new LongName("rewrite"),
        "`rewrite (p : a = b) t : T` replaces occurrences of `a` in `T` with a variable `x` obtaining a type `T[x/a]` and returns `transport (\\lam x => T[x/a]) p t`\n\n" +
        "If the expected type is unknown, {rewrite} works like {rewriteF}.\n" +
        "`rewrite {i_1, ... i_k} p t` replaces only occurrences with indices `i_1`, ... `i_k`.\n" +
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
    contributor.declare(algebra, new LongName("equation"),
        "`equation a_1 ... a_n` proves an equation a_0 = a_{n+1} using a_1, ... a_n as intermediate steps\n\n" +
        "A proof of a_i = a_{i+1} can be specified as implicit arguments between them\n" +
        "`using`, `usingOnly`, and `hiding` with a single argument can be used instead of a proof to control the context",
        Precedence.DEFAULT, new DeferredMetaDefinition(equationMeta, true));

    contributor.declare(algebra, new LongName("congruence"),
        "",
        Precedence.DEFAULT, new DeferredMetaDefinition(new CongruenceMeta(this), true));

    ModulePath logic = ModulePath.fromString("Logic.Meta");
    contributor.declare(logic, new LongName("contradiction"),
        "Derives a contradiction from assumptions in the context\n\n" +
        "A proof of a contradiction can be explicitly specified as an implicit argument\n" +
        "`using`, `usingOnly`, and `hiding` with a single argument can be used instead of a proof to control the context",
        Precedence.DEFAULT, contradictionMeta);
    contributor.declare(logic, new LongName("Exists"),
      "`Exists (x y z : A) B` is equivalent to `TruncP (\\Sigma (x y z : A) B)`.\n" +
      "`Exists {x y z} B` is equivalent to `TruncP (\\Sigma (x y z : _) B)`", Precedence.DEFAULT, "∃", Precedence.DEFAULT, null, new ExistsMeta(this));

    ModulePath debug = ModulePath.fromString("Debug.Meta");
    contributor.declare(debug, new LongName("time"), "Returns current time in milliseconds", Precedence.DEFAULT, new TimeMeta(this));
    contributor.declare(debug, new LongName("println"), "Prints the argument to the console", Precedence.DEFAULT, new PrintMeta(this));
    contributor.declare(debug, new LongName("random"),
      "`random` returns a random number.\n" +
      "`random n` returns a random number between 0 and `n`.\n" +
      "`random (l,u)` returns a random number between `l` and `u`.",
      Precedence.DEFAULT, new RandomMeta(this));
  }

  @Override
  public @Nullable StdGoalSolver getGoalSolver() {
    return goalSolver;
  }

  @Override
  public @Nullable LevelProver getLevelProver() {
    return levelProver;
  }

  @Override
  public @Nullable LiteralTypechecker getLiteralTypechecker() {
    return numberTypechecker;
  }

  @Override
  public @Nullable DefinitionListener getDefinitionListener() {
    return definitionListener;
  }
}
