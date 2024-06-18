package org.arend.lib;

import org.arend.ext.*;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.ops.NormalizationMode;
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
import org.arend.lib.meta.linear.LinearSolverMeta;
import org.arend.lib.meta.simplify.SimplifyMeta;
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
  @Dependency(module = "Paths")              public CoreFunctionDefinition pmap;

  @Dependency(module = "Data.List", name = "List.nil") public CoreConstructor nil;
  @Dependency(module = "Data.List", name = "List.::")  public CoreConstructor cons;
  @Dependency(module = "Data.List", name = "++")       public CoreFunctionDefinition append;

  @Dependency(module = "Logic")                       public CoreDataDefinition Empty;
  @Dependency(module = "Logic")                       public CoreDataDefinition TruncP;
  @Dependency(module = "Logic")                       public CoreFunctionDefinition propExt;
  @Dependency(module = "Logic", name = "prop-isProp") public CoreFunctionDefinition propIsProp;
  @Dependency(module = "Logic", name = "prop-dpi")    public CoreFunctionDefinition propDPI;

  @Dependency(module = "Algebra.Pointed")                          public CoreClassDefinition Pointed;
  @Dependency(module = "Algebra.Pointed")                          public CoreClassDefinition AddPointed;
  @Dependency(module = "Algebra.Pointed", name = "Pointed.ide")    public CoreClassField ide;
  @Dependency(module = "Algebra.Pointed", name = "AddPointed.zro") public CoreClassField zro;

  @Dependency(module = "Data.Bool")                       public CoreDataDefinition Bool;
  @Dependency(module = "Data.Bool", name = "Bool.true")   public CoreConstructor true_;

  public final EquationMeta equationMeta = new EquationMeta(this);
  public final LinearSolverMeta linearSolverMeta = new LinearSolverMeta(this);
  public final ContradictionMeta contradictionMeta = new ContradictionMeta(this);
  public final ExtMeta extMeta = new ExtMeta(this, false);
  public final ExtMeta extsMeta = new ExtMeta(this, true);
  public final LaterMeta laterMeta = new LaterMeta();
  public final SimpCoeMeta simpCoeMeta = new SimpCoeMeta(this, false);
  public final SimpCoeMeta simpCoeFMeta = new SimpCoeMeta(this, true);
  public final SIPMeta sipMeta = new SIPMeta(this);
  public CasesMeta casesMeta;
  public MetaRef constructorMetaRef;

  public MetaRef givenMetaRef;
  public MetaRef forallMetaRef;
  public MetaRef existsMetaRef;

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
    simpCoeFMeta.transport_path_pmap = provider.getDefinition(new ModulePath("Paths"), LongName.fromString("transport_path_pmap.conv"), CoreFunctionDefinition.class);
    simpCoeFMeta.transport_path_pmap_right = provider.getDefinition(new ModulePath("Paths"), LongName.fromString("transport_path_pmap-right.conv"), CoreFunctionDefinition.class);
    provider.load(sipMeta);
    provider.getDefinition(new ModulePath("Set"), new LongName("ProductDecide"), CoreFunctionDefinition.class);
    provider.getDefinition(new ModulePath("Set"), new LongName("NotDecide"), CoreFunctionDefinition.class);
    provider.getDefinition(new ModulePath("Set"), new LongName("EqualityDecide"), CoreFunctionDefinition.class);
    provider.getDefinition(ModulePath.fromString("Data.List"), new LongName("ListMonoid"), CoreFunctionDefinition.class);
    provider.getDefinition(ModulePath.fromString("Arith.Nat"), new LongName("NatSemiring"), CoreFunctionDefinition.class);
    provider.getDefinition(ModulePath.fromString("Arith.Int"), new LongName("IntRing"), CoreFunctionDefinition.class);
    provider.getDefinition(ModulePath.fromString("Order.Lexicographical"), new LongName("LexicographicalProduct"), CoreFunctionDefinition.class);
    provider.getDefinition(ModulePath.fromString("Order.Lexicographical"), new LongName("LexicographicalList"), CoreFunctionDefinition.class);
    provider.getDefinition(ModulePath.fromString("Algebra.Domain.Euclidean"), new LongName("NatEuclidean"), CoreFunctionDefinition.class);
    provider.getDefinition(ModulePath.fromString("Algebra.Monoid.GCD"), LongName.fromString("DivQuotient.DivQuotientGCDMonoid"), CoreFunctionDefinition.class);
    provider.load(equationMeta);
    provider.load(linearSolverMeta);
  }

  @Override
  public void declareDefinitions(@NotNull DefinitionContributor contributor) {
    ModulePath meta = new ModulePath("Meta");
    contributor.declare(meta, new LongName("later"), "`later meta args` defers the invocation of `meta args`", Precedence.DEFAULT, laterMeta);
    contributor.declare(meta, new LongName("fails"),
      """
        `fails meta args` succeeds if and only if `meta args` fails

        `fails {T} meta args` succeeds if and only if `meta args : T` fails
        """, Precedence.DEFAULT, new FailsMeta(this));
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
    contributor.declare(meta, new LongName("at"), "`((f_1, ... f_n) at x) r` replaces variable `x` with `f_1 (... (f_n x) ...)` and runs `r` in the modified context", new Precedence(Precedence.Associativity.NON_ASSOC, (byte) 1, true), new AtMeta(this));
    contributor.declare(meta, new LongName("in"), "`f in x` is equivalent to `\\let r => f x \\in r`. Also, `(f_1, ... f_n) in x` is equivalent to `f_1 in ... f_n in x`. This meta is usually used with `f` being a meta such as `rewrite`, `simplify`, `simp_coe`, or `unfold`.", new Precedence(Precedence.Associativity.RIGHT_ASSOC, (byte) 1, true), new InMeta(this));
    casesMeta = new CasesMeta(this);
    contributor.declare(meta, new LongName("cases"),
      """
        `cases args default` works just like `mcases args default`, but does not search for \\case expressions or definition invocations.
        Each argument has a set of parameters that can be configured.
        Parameters are specified after keyword 'arg' which is written after the argument.
        Available parameters are 'addPath', 'name', and 'as'.
        Parameter 'name' can be used to specify the name of the argument which can be used in types of subsequent arguments.
        Parameter 'as' can be used to specify an \\as-name that will be added to corresponding patterns in each clause.
        The type of an argument is specified as either `e : E` or `e arg parameters : E`.
        The flag 'addPath' indicates that argument `idp` with type `e = x` should be added after the current one, where `e` is the current argument and `x` is its name.
        That is, `cases (e arg addPath)` is equivalent to `cases (e arg (name = x), idp : e = x)`.
        """, Precedence.DEFAULT, casesMeta);
    contributor.declare(meta, new LongName("mcases"),
      """
        `mcases {def} args default \\with { ... }` finds all invocations of definition `def` in the expected type and generate a \\case expression that matches arguments of those invocations.

        It matches only those arguments which are matched in `def`.
        If the explicit argument is omitted, then `mcases` searches for \\case expressions instead of definition invocations.
        `default` is an optional argument which is used as a default result for missing clauses.
        The list of clauses after \\with can be omitted if the default expression is specified.
        `args` is a comma-separated list of expressions (which can be omitted) that will be additionally matched in the resulting \\case expressions.
        These arguments are written in the same syntax as arguments in `cases`.
        `mcases` also searches for occurrences of `def` in the types of these additional expressions.
        Parameters of found arguments can be specified in the second implicit argument.
        The syntax is similar to the syntax for arguments in `cases`, but the expression should be omitted.
        If the first implicit argument is `_`, it will be skipped.
        `mcases {def_1, ... def_n}` searches for occurrences of definitions `def_1`, ... `def_n`.
        `mcases {def, i_1, ... i_n}` matches arguments only of `i_1`-th, ... `i_n`-th occurrences of `def`.
        For example,
        * `mcases {(def1,4),def2,(def3,1,2)}` looks for the 4th occurrence of `def1`, all occurrences of `def2`, and the first and the second occurrence of `def3`.
        * `mcases {(1,2),(def,1)}` looks for the first and the second occurrence of a \\case expression and the first occurrence of `def`.
        * `mcases {(def1,2),(),def2}` looks for the second occurrence of `def1`, all occurrences of \\case expressions, and all occurrences of `def2`.
        * `mcases {_} {arg addPath, arg (), arg addPath}` looks for case expressions and adds a path argument after the first and the third matched expression.
        """, Precedence.DEFAULT, new MatchingCasesMeta(this));
    contributor.declare(meta, new LongName("unfold"),
      """
        `unfold (f_1, ... f_n) e` unfolds functions/fields/variables `f_1`, ... `f_n` in the expected type before type-checking of `e` and returns `e` itself.
        If the first argument is omitted, it unfold all fields.
        If the expected type is unknown, it unfolds these function in the result type of `e`.
        """, Precedence.DEFAULT, new DeferredMetaDefinition(new UnfoldMeta(this), true, false));
    contributor.declare(meta, new LongName("unfold_let"), "Unfolds \\let expressions", Precedence.DEFAULT, new DeferredMetaDefinition(new UnfoldLetMeta(), true, false));
    contributor.declare(meta, new LongName("unfolds"), "Unfolds recursively top-level functions and fields", Precedence.DEFAULT, new DeferredMetaDefinition(new UnfoldsMeta(), true, false));
    contributor.declare(meta, new LongName("<|>"),
      "`x <|> y` invokes `x` and if it fails, invokes `y`\n" +
      "Also, `(x <|> y) z_1 ... z_n` is equivalent to `x z_1 ... z_n <|> z_1 ... z_n`", new Precedence(Precedence.Associativity.RIGHT_ASSOC, (byte) 3, true), new OrElseMeta(this));
    contributor.declare(meta, new LongName("try"), "The same as {<|>}", Precedence.DEFAULT, new OrElseMeta(this));
    contributor.declare(meta, new LongName("mkcon"),
      "Inserts data type arguments in constructor invocation.\n" +
      "If constructor `con` has 3 data type arguments, then `mkcon con args` is equivalent to `con {_} {_} {_} args`", Precedence.DEFAULT, new MakeConstructorMeta(this));
    contributor.declare(meta, new LongName("assumption"),
      """
        * `assumption` searches for a proof in the context. It tries variables that are declared later first.
        * `assumption` {n} returns the n-th variables from the context counting from the end.
        * `assumption` {n} a1 ... ak applies n-th variable from the context to arguments a1, ... ak.
        """, Precedence.DEFAULT, new AssumptionMeta(this));
    contributor.declare(meta, new LongName("defaultImpl"), "`defaultImpl C F E` returns the default implementation of field `F` in class `C` applied to expression `E`. The third argument can be omitted, in which case either `\\this` or `_` will be used instead,", Precedence.DEFAULT, new DefaultImplMeta(this));

    ModulePath paths = ModulePath.fromString("Paths.Meta");
    contributor.declare(paths, new LongName("rewrite"),
      """
        `rewrite (p : a = b) t : T` replaces occurrences of `a` in `T` with a variable `x` obtaining a type `T[x/a]` and returns `transportInv (\\lam x => T[x/a]) p t`

        If the expected type is unknown, the meta rewrites in the type of the arguments instead.
        `rewrite {i_1, ... i_k} p t` replaces only occurrences with indices `i_1`, ... `i_k`. Here `i_j` is the number of occurrence after replacing all the previous occurrences.\s
        Also, `p` may be a function, in which case `rewrite p` is equivalent to `rewrite (p _ ... _)`.
        `rewrite (p_1, ... p_n) t` is equivalent to `rewrite p_1 (... rewrite p_n t ...)`
        """, Precedence.DEFAULT, new RewriteMeta(this, false, true, false));
    contributor.declare(paths, new LongName("rewriteI"),
        "`rewriteI p` is equivalent to `rewrite (inv p)`",
        Precedence.DEFAULT, new RewriteMeta(this, false, false, false));
    contributor.declare(paths, new LongName("rewriteEq"),
      """
        `rewriteEq (p : a = b) t : T` is similar to {rewrite}, but it finds and replaces occurrences of `a` up to algebraic equivalences.
        For example, `rewriteEq (p : b * (c * id) = x) t : T` rewrites `(a * b) * (id * c)` as `a * x` in `T`.\s
        Similarly to `rewrite` this meta allows specification of occurrence numbers.\s
        Currently this meta supports noncommutative monoids and categories.
        """, Precedence.DEFAULT, new RewriteMeta(this, false, true, true));
    contributor.declare(paths, new LongName("simplify"), "Simplifies the expected type or the type of the argument if the expected type is unknown.", Precedence.DEFAULT, new DeferredMetaDefinition(new SimplifyMeta(this), true));
    contributor.declare(paths, new LongName("simp_coe"),
      """
        Simplifies certain equalities. It expects one argument and the type of this argument is called 'subgoal'. The expected type is called 'goal'.
        * If the goal is `coe (\\lam i => \\Pi (x : A) -> B x i) f right a = b'`, then the subgoal is `coe (B a) (f a) right = b`.
        * If the goal is `coe (\\lam i => \\Pi (x : A) -> B x i) f right = g'`, then the subgoal is `\\Pi (a : A) -> coe (B a) (f a) right = g a`.
        * If the goal is `coe (\\lam i => A i -> B i) f right = g'`, then the subgoal is `\\Pi (a : A left) -> coe B (f a) right = g (coe A a right)`.
        * If the type under `coe` is a higher-order non-dependent function type, `simp_coe` simplifies it recursively.
        * If the goal is `(coe (\\lam i => \\Sigma (x_1 : A_1 i) ... (x_n : A_n i) ...) t right).n = b'`, then the subgoal is `coe A_n t.n right = b`.
        * If the goal is `coe (\\lam i => \\Sigma (x_1 : A_1) ... (x_n : A_n) (B_{n+1} i) ... (B_k i)) t right = s'`, then the subgoal is a \\Sigma type consisting of equalities as specified above ignoring fields in \\Prop.
        * If the type under `coe` is a record, then `simp_coe` works similarly to the case of \\Sigma types. The copattern matching syntax as in {ext} is also supported.
        * All of the above cases also work for goals with {transport} instead of {coe} since the former evaluates to the latter.
        * If the goal is `transport (\\lam x => f x = g x) p q = s`, then the subgoal is `q *> pmap g p = pmap f p *> s`. If `f` does not depend on `x`, then the right hand side of the subgoal is simply `s`.
        If the expected type is unknown or if the meta is applied to more than one argument, then it applies to the type of the argument instead of the expected type.
        """, Precedence.DEFAULT, null, null, simpCoeMeta, new ClassExtResolver(this));
    contributor.declare(paths, new LongName("ext"),
      """
        Proves goals of the form `a = {A} a'`. It expects (at most) one argument and the type of this argument is called 'subgoal'. The expected type is called 'goal'
        * If the goal is `f = {\\Pi (x_1 : A_1) ... (x_n : A_n) -> B} g`, then the subgoal is `\\Pi (x_1 : A_1) ... (x_n : A_n) -> f x_1 ... x_n = g x_1 ... x_n`
        * If the goal is `t = {\\Sigma (x_1 : A_1) ... (x_n : A_n) (y_1 : B_1 x_1 ... x_n) ... (y_k : B_k x_1 ... x_n) (z_1 : C_1) ... (z_m : C_m)} s`, where `C_i : \\Prop` and they can depend on `x_j` and `y_l` for all `i`, `j`, and `l`, then the subgoal is `\\Sigma (p_1 : t.1 = s.1) ... (p_n : t.n = s.n) D_1 ... D_k`, where `D_j` is equal to `coe (\\lam i => B (p_1 @ i) ... (p_n @ i)) t.{k + j - 1} right = s.{k + j - 1}`
        * If the goal is `t = {R} s`, where `R` is a record, then the subgoal is defined in the same way as for \\Sigma-types It is also possible to use the following syntax in this case: `ext R { | f_1 => e_1 ... | f_l => e_l }`, which is equivalent to `ext (e_1, ... e_l)`
        * If the goal is `A = {\\Prop} B`, then the subgoal is `\\Sigma (A -> B) (B -> A)`
        * If the goal is `A = {\\Type} B`, then the subgoal is `Equiv {A} {B}`
        * If the goal is `x = {P} y`, where `P : \\Prop`, then the argument for {ext} should be omitted
        """, Precedence.DEFAULT, null, null, new DeferredMetaDefinition(extMeta, false, ExtMeta.defermentChecker), new ClassExtResolver(this));
    contributor.declare(paths, new LongName("exts"),
      "Similar to {ext}, but also applies either {simp_coe} or {ext} when a field of a \\Sigma-type or a record has an appropriate type.",
      Precedence.DEFAULT, null, null, new DeferredMetaDefinition(extsMeta, false, ExtMeta.defermentChecker), new ClassExtResolver(this));

    MetaDefinition apply = new ApplyMeta(this);
    ModulePath function = ModulePath.fromString("Function.Meta");
    contributor.declare(function, new LongName("$"), "`f $ a` returns `f a`", new Precedence(Precedence.Associativity.RIGHT_ASSOC, (byte) 0, true), apply);
    contributor.declare(function, new LongName("#"), "`f # a` returns `f a`", new Precedence(Precedence.Associativity.LEFT_ASSOC, (byte) 0, true), apply);
    contributor.declare(function, new LongName("repeat"),
      """
        `repeat {n} f x` returns `f^n(x)

        ``repeat f x` repeats `f` until it fails and returns `x` in this case
        """, Precedence.DEFAULT, new RepeatMeta(this));

    ModulePath algebra = ModulePath.fromString("Algebra.Meta");
    contributor.declare(algebra, new LongName("equation"),
      """
        `equation a_1 ... a_n` proves an equation a_0 = a_{n+1} using a_1, ... a_n as intermediate steps

        A proof of a_i = a_{i+1} can be specified as implicit arguments between them.
        `using`, `usingOnly`, and `hiding` with a single argument can be used instead of a proof to control the context.
        The first implicit argument can be either a universe or a subclass of either {Algebra.Monoid.Monoid}, {Algebra.Monoid.AddMonoid}, or {Order.Lattice.Bounded.MeetSemilattice}.
        In the former case, the meta will prove an equality in a type without using any additional structure on it.
        In the latter case, the meta will prove an equality using only structure available in the specified class.
        """, Precedence.DEFAULT, new DeferredMetaDefinition(equationMeta, true));
    contributor.declare(algebra, new LongName("linarith"), "Solve systems of linear equations", Precedence.DEFAULT, new DeferredMetaDefinition(linearSolverMeta, true));
    contributor.declare(algebra, new LongName("cong"),
        "Proves an equality by congruence closure of equalities in the context. E.g. derives f a = g b from f = g and a = b",
        Precedence.DEFAULT, new DeferredMetaDefinition(new CongruenceMeta(this)));

    ModulePath logic = ModulePath.fromString("Logic.Meta");
    contributor.declare(logic, new LongName("contradiction"),
      """
        Derives a contradiction from assumptions in the context

        A proof of a contradiction can be explicitly specified as an implicit argument
        `using`, `usingOnly`, and `hiding` with a single argument can be used instead of a proof to control the context
        """, Precedence.DEFAULT, contradictionMeta);
    givenMetaRef = contributor.declare(logic, new LongName("Given"),
      """
        Given constructs a \\Sigma-type:
        * `Given (x y z : A) B` is equivalent to `\\Sigma (x y z : A) B`.
        * `Given {x y z} B` is equivalent to `\\Sigma (x y z : _) B`
        * If `P : A -> B -> C -> \\Type`, then `Given ((x,y,z) (a,b,c) : P) (Q x y z a b c)` is equivalent to `\\Sigma (x a : A) (y b : B) (z c : C) (P x y z) (P a b c) (Q x y z a b c)`
        * If `l : Array A`, then `Given (x y : l) (P x y)` is equivalent to `\\Sigma (j j' : Fin l.len) (P (l j) (l j'))`
        """, Precedence.DEFAULT, new ExistsMeta(this, ExistsMeta.Kind.SIGMA));
    existsMetaRef = contributor.declare(logic, new LongName("Exists"),
      "{Exists} is a truncated version of {Given}. That is, `Exists a b c` is equivalent to `TruncP (Given a b c)`",
      Precedence.DEFAULT, "∃", Precedence.DEFAULT, new ExistsMeta(this, ExistsMeta.Kind.TRUNCATED));
    forallMetaRef = contributor.declare(logic, new LongName("Forall"),
      """
        {Forall} works like {Given}, but returns a \\Pi-type instead of a \\Sigma-type.
        The last argument should be a type and will be used as the codomain.
        Other arguments work like arguments of {Given} with the exception that curly braces mean implicit arguments:
        * `Forall (x y : A) B` is equivalent to `\\Pi (x y : A) -> B`
        * `Forall {x y : A} B` is equivalent to `\\Pi {x y : A} -> B`
        * `Forall x y B` is equivalent to `\\Pi (x : _) (y : _) -> B
        `* `Forall x (B 0) (B 1)` is equivalent to `\\Pi (x : _) -> B 0 -> B 1
        `* `Forall {x y} {z} B` is equivalent to `\\Pi {x y : _} {z : _} -> B`
        * If `P : A -> \\Type`, then `Forall {x y : P} (Q x) (Q y)` is equivalent to `\\Pi {x y : A} -> P x -> P y -> Q x -> Q y`
        """, Precedence.DEFAULT, "∀", Precedence.DEFAULT, new ExistsMeta(this, ExistsMeta.Kind.PI));
    constructorMetaRef = contributor.declare(logic, new LongName("constructor"),
      "Returns either a tuple, a \\new expression, or a single constructor of a data type depending on the expected type",
      Precedence.DEFAULT, new ConstructorMeta(this, false));

    ModulePath debug = ModulePath.fromString("Debug.Meta");
    contributor.declare(debug, new LongName("time"), "Returns current time in milliseconds", Precedence.DEFAULT, new TimeMeta(this));
    contributor.declare(debug, new LongName("println"), "Prints the argument to the console", Precedence.DEFAULT, new PrintMeta(this));
    contributor.declare(debug, new LongName("random"),
      """
        `random` returns a random number.
        `random n` returns a random number between 0 and `n`.
        `random (l,u)` returns a random number between `l` and `u`.
        """, Precedence.DEFAULT, new RandomMeta(this));
    contributor.declare(debug, new LongName("nf"), "Normalizes the argument", Precedence.DEFAULT, new NormalizationMeta(NormalizationMode.ENF));
    contributor.declare(debug, LongName.fromString("nf.whnf"), "", Precedence.DEFAULT, new NormalizationMeta(NormalizationMode.WHNF));
    contributor.declare(debug, LongName.fromString("nf.rnf"), "", Precedence.DEFAULT, new NormalizationMeta(NormalizationMode.RNF));

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
