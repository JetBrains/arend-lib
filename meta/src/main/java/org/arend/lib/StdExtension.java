package org.arend.lib;

import org.arend.ext.*;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.core.definition.*;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.dependency.ArendDependencyProvider;
import org.arend.ext.module.LongName;
import org.arend.ext.module.ModulePath;
import org.arend.ext.reference.MetaRef;
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
import org.arend.lib.meta.cong.CongruenceMeta;
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

  @Dependency(module = "Set")                     public CoreClassDefinition BaseSet;
  @Dependency(module = "Set", name = "BaseSet.E") public CoreClassField carrier;

  @Dependency(module = "Paths")              public CoreFunctionDefinition transport;
  @Dependency(module = "Paths")              public CoreFunctionDefinition transportInv;
  @Dependency(module = "Paths", name = "*>") public CoreFunctionDefinition concat;
  @Dependency(module = "Paths")              public CoreFunctionDefinition inv;
  @Dependency(module = "Paths")              public CoreFunctionDefinition Jl;
  @Dependency(module = "Paths")              public CoreFunctionDefinition pathOver;
  @Dependency(module = "Paths")              public CoreFunctionDefinition pathInProp;

  @Dependency(module = "Data.List", name = "List.nil") public CoreConstructor nil;
  @Dependency(module = "Data.List", name = "List.::")  public CoreConstructor cons;
  @Dependency(module = "Data.List", name = "++")       public CoreFunctionDefinition append;

  @Dependency(module = "Logic") public CoreDataDefinition Empty;
  @Dependency(module = "Logic") public CoreDataDefinition TruncP;
  @Dependency(module = "Logic") public CoreFunctionDefinition propExt;

  public final EquationMeta equationMeta = new EquationMeta(this);
  public final ContradictionMeta contradictionMeta = new ContradictionMeta(this);
  public final ExtMeta extMeta = new ExtMeta(this, false);
  public final ExtMeta extsMeta = new ExtMeta(this, true);
  public final SimpCoeMeta simpCoeMeta = new SimpCoeMeta(this);
  public final SIPMeta sipMeta = new SIPMeta(this);
  public CasesMeta casesMeta;
  public MetaRef constructorMetaRef;

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
    provider.load(simpCoeMeta);
    provider.load(sipMeta);
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
    casesMeta = new CasesMeta(this);
    contributor.declare(meta, new LongName("cases"),
      "`cases args default` works just like `mcases args default`, but does not search for \\case expressions or definition invocations.\n" +
      "Each argument has a set of parameters that can be configured.\n" +
      "Parameters are specified after keyword 'arg' which is written after the argument.\n" +
      "Available parameters are 'addPath' and 'name'.\n" +
      "The latter can be used to specify the name of the argument which can be used in types of subsequent arguments.\n" +
      "The type of an argument is specified as either `e : E` or `e arg parameters : E`.\n" +
      "The flag 'addPath' indicates that argument `idp` with type `e = x` should be added after the current one, where `e` is the current argument and `x` is its name.\n" +
      "That is, `cases (e arg addPath)` is equivalent to `cases (e arg (name = x), idp : e = x)`",
      Precedence.DEFAULT, casesMeta);
    contributor.declare(meta, new LongName("mcases"),
      "`mcases {def} args default \\with { ... }` finds all invocations of definition `def` in the expected type and generate a \\case expression that matches arguments of those invocations.\n\n" +
      "It matches only those arguments which are matched in `def`.\n" +
      "If the explicit argument is omitted, then `mcases` searches for \\case expressions instead of definition invocations.\n" +
      "`default` is an optional argument which is used as a default result for missing clauses.\n" +
      "The list of clauses after \\with can be omitted if the default expression is specified.\n" +
      "`args` is a comma-separated list of expressions (which can be omitted) that will be additionally matched in the resulting \\case expressions.\n" +
      "These arguments are written in the same syntax as arguments in `cases`.\n" +
      "`mcases` also searches for occurrences of `def` in the types of these additional expressions.\n" +
      "Parameters of found arguments can be specified in the second implicit argument.\n" +
      "The syntax is similar to the syntax for arguments in `cases`, but the expression should be omitted.\n" +
      "If the first implicit argument is `_`, it will be skipped.\n" +
      "`mcases {def_1, ... def_n}` searches for occurrences of definitions `def_1`, ... `def_n`\n" +
      "`mcases {def, i_1, ... i_n}` matches arguments only of `i_1`-th, ... `i_n`-th occurrences of `def`\n" +
      "For example\n" +
      "* `mcases {(def1,4),def2,(def3,1,2)}` looks for the 4th occurrence of `def1`, all occurrences of `def2`, and the first and the second occurrence of `def3`\n" +
      "* `mcases {(1,2),(def,1)}` looks for the first and the second occurrence of a \\case expression and the first occurrence of `def`\n" +
      "* `mcases {(def1,2),(),def2}` looks for the second occurrence of `def1`, all occurrences of \\case expressions, and all occurrences of `def2`\n" +
      "* `mcases {_} {arg addPath, arg (), arg addPath}` looks for case expressions and adds a path argument after the first and the third matched expression",
      Precedence.DEFAULT, new MatchingCasesMeta(this));
    contributor.declare(meta, new LongName("unfold"),
      "`unfold (f_1, ... f_n) e` unfolds functions f_1, ... f_n in the expected type before type-checking of `e` and returns `e` itself.\n" +
      "If the expected type is unknown, it unfolds these function in the result type of `e`.",
      Precedence.DEFAULT, new DeferredMetaDefinition(new UnfoldMeta(this), false, ExpressionTypechecker.Stage.AFTER_LEVELS));

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
        "`rewriteF (p : a = b) e` is similar to {rewrite}, but it replaces occurrences of `a` in the type of `e` instead of the expected type",
        Precedence.DEFAULT, new RewriteMeta(this, true, false));
    contributor.declare(paths, new LongName("simp_coe"),
      "Simplifies certain equalities. It expects one argument and the type of this argument is called 'subgoal'. The expected type is called 'goal'.\n" +
      "* If the goal is `coe (\\lam i => \\Pi (x : A) -> B x i) f right a = b'`, then the subgoal is `coe (B a) (f a) right = b`.\n" +
      "* If the goal is `coe (\\lam i => \\Pi (x : A) -> B x i) f right = g'`, then the subgoal is `\\Pi (a : A) -> coe (B a) (f a) right = g a`.\n" +
      "* If the goal is `coe (\\lam i => A i -> B i) f right = g'`, then the subgoal is `\\Pi (a : A left) -> coe B (f a) right = g (coe A a right)`.\n" +
      "* If the type under `coe` is a higher-order non-dependent function type, `simp_coe` simplifies it recursively.\n" +
      "* If the goal is `(coe (\\lam i => \\Sigma (x_1 : A_1 i) ... (x_n : A_n i) ...) t right).n = b'`, then the subgoal is `coe A_n t.n right = b`.\n" +
      "* If the goal is `coe (\\lam i => \\Sigma (x_1 : A_1) ... (x_n : A_n) (B_{n+1} i) ... (B_k i)) t right = s'`, then the subgoal is a \\Sigma type consisting of equalities as specified above ignoring fields in \\Prop.\n" +
      "* If the type under `coe` is a record, then `simp_coe` works similarly to the case of \\Sigma types. The copattern matching syntax as in {ext} is also supported.\n" +
      "* All of the above cases also work for goals with {transport} instead of {coe} since the former evaluates to the latter.\n" +
      "* If the goal is `transport (\\lam x => f x = g x) p q = s`, then the subgoal is `q *> pmap g p = pmap f p *> s`. If `f` does not depend on `x`, then the right hand side of the subgoal is simply `s`.",
      Precedence.DEFAULT, null, null, simpCoeMeta, new ClassExtResolver(this));
    contributor.declare(paths, new LongName("ext"),
      "Proves goals of the form `a = {A} a'`. It expects (at most) one argument and the type of this argument is called 'subgoal'. The expected type is called 'goal'.\n" +
      "* If the goal is `f = {\\Pi (x_1 : A_1) ... (x_n : A_n) -> B} g`, then the subgoal is `\\Pi (x_1 : A_1) ... (x_n : A_n) -> f x_1 ... x_n = g x_1 ... x_n`\n" +
      "* If the goal is `t = {\\Sigma (x_1 : A_1) ... (x_n : A_n) (y_1 : B_1 x_1 ... x_n) ... (y_k : B_k x_1 ... x_n) (z_1 : C_1) ... (z_m : C_m)} s`, where `C_i : \\Prop` and they can depend on on `x_j` and `y_l` for all `i`, `j`, and `l`," +
        " then the subgoal is `\\Sigma (p_1 : t.1 = s.1) ... (p_n : t.n = s.n) D_1 ... D_k`, where `D_j` is equal to `coe (\\lam i => B (p_1 @ i) ... (p_n @ i)) t.{k + j - 1} right = s.{k + j - 1}`.\n" +
      "* If the goal is `t = {R} s`, where `R` is a record, then the subgoal is defined in the same way as for \\Sigma-types." +
        " It is also possible to use the following syntax in this case: `ext R { | f_1 => e_1 ... | f_l => e_l }`, which is equivalent to `ext (e_1, ... e_l)`\n" +
      "* If the goal is `A = {\\Prop} B`, then the subgoal is `\\Sigma (A -> B) (B -> A)`\n" +
      "* If the goal is `A = {\\Type} B`, then the subgoal is `Equiv {A} {B}`\n" +
      "* If the goal is `x = {P} y`, where `P : \\Prop`, then the argument for {ext} should be omitted.",
      Precedence.DEFAULT, null, null, new DeferredMetaDefinition(extMeta, false, ExpressionTypechecker.Stage.AFTER_LEVELS), new ClassExtResolver(this));
    contributor.declare(paths, new LongName("exts"),
      "Similar to {ext}, but also applies either {simp_coe} or {ext} when a field of a \\Sigma-type or a record has an appropriate type.",
      Precedence.DEFAULT, null, null, new DeferredMetaDefinition(extsMeta, false, ExpressionTypechecker.Stage.AFTER_LEVELS), new ClassExtResolver(this));

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
        "`using`, `usingOnly`, and `hiding` with a single argument can be used instead of a proof to control the context.\n" +
        "The first implicit argument can be either a universe or a subclass of either {Algebra.Monoid.Monoid}, {Algebra.Monoid.AddMonoid}, or {Order.Lattice.Bounded.MeetSemilattice}.\n" +
        "In the former case, the meta will prove an equality in a type without using any additional structure on it.\n" +
        "In the latter case, the meta will prove an equality using only structure available in the specified class.",
        Precedence.DEFAULT, new DeferredMetaDefinition(equationMeta, true));
    contributor.declare(algebra, new LongName("cong"),
        "Proves an equality by congruence closure of equalities in the context. E.g. derives f a = g b from f = g and a = b",
        Precedence.DEFAULT, new DeferredMetaDefinition(new CongruenceMeta(this)));

    ModulePath logic = ModulePath.fromString("Logic.Meta");
    contributor.declare(logic, new LongName("contradiction"),
        "Derives a contradiction from assumptions in the context\n\n" +
        "A proof of a contradiction can be explicitly specified as an implicit argument\n" +
        "`using`, `usingOnly`, and `hiding` with a single argument can be used instead of a proof to control the context",
        Precedence.DEFAULT, contradictionMeta);
    contributor.declare(logic, new LongName("Exists"),
      "`Exists (x y z : A) B` is equivalent to `TruncP (\\Sigma (x y z : A) B)`.\n" +
      "`Exists {x y z} B` is equivalent to `TruncP (\\Sigma (x y z : _) B)`", Precedence.DEFAULT, "∃", Precedence.DEFAULT, new ExistsMeta(this));
    constructorMetaRef = contributor.declare(logic, new LongName("constructor"),
      "Returns either a tuple, a \\new expression, or a single constructor of a data type depending on the expected type",
      Precedence.DEFAULT, new ConstructorMeta(this, false));

    ModulePath debug = ModulePath.fromString("Debug.Meta");
    contributor.declare(debug, new LongName("time"), "Returns current time in milliseconds", Precedence.DEFAULT, new TimeMeta(this));
    contributor.declare(debug, new LongName("println"), "Prints the argument to the console", Precedence.DEFAULT, new PrintMeta(this));
    contributor.declare(debug, new LongName("random"),
      "`random` returns a random number.\n" +
      "`random n` returns a random number between 0 and `n`.\n" +
      "`random (l,u)` returns a random number between `l` and `u`.",
      Precedence.DEFAULT, new RandomMeta(this));

    ModulePath category = ModulePath.fromString("Category.Meta");
    contributor.declare(category, new LongName("sip"),
      "Proves univalence for categories. The type of objects must extend `BaseSet` and the Hom-set must extend `SetHom` with properties only.",
      Precedence.DEFAULT, sipMeta);
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
