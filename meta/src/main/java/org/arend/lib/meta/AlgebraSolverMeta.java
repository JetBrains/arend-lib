package org.arend.lib.meta;

import org.arend.ext.concrete.*;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFieldCallExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.TypeMismatchError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.arend.lib.error.AlgebraSolverError;
import org.arend.lib.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

import static java.util.Collections.singletonList;

public class AlgebraSolverMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  @Dependency(module = "Algebra.Monoid", name = "Monoid")      private CoreClassDefinition monoid;
  @Dependency(module = "Algebra.Monoid", name = "Monoid.E")    private CoreClassField carrier;
  @Dependency(module = "Algebra.Monoid", name = "Monoid.ide")  private CoreClassField ide;
  @Dependency(module = "Algebra.Monoid", name = "Monoid.*")    private CoreClassField mul;
  @Dependency(module = "Algebra.Monoid", name = "Monoid.LDiv") private CoreClassDefinition ldiv;
  @Dependency(module = "Algebra.Monoid", name = "Monoid.RDiv") private CoreClassDefinition rdiv;

  @Dependency(module = "Algebra.Monoid.Solver", name = "MonoidTerm.var")  private CoreConstructor varTerm;
  @Dependency(module = "Algebra.Monoid.Solver", name = "MonoidTerm.:ide") private CoreConstructor ideTerm;
  @Dependency(module = "Algebra.Monoid.Solver", name = "MonoidTerm.:*")   private CoreConstructor mulTerm;

  @Dependency(module = "Algebra.Monoid.Solver", name = "Data")                     private CoreClassDefinition dataClass;
  @Dependency(module = "Algebra.Monoid.Solver", name = "Data.terms-equality")      private CoreFunctionDefinition termsEq;
  @Dependency(module = "Algebra.Monoid.Solver", name = "Data.terms-equality-conv") private CoreFunctionDefinition termsEqConv;
  @Dependency(module = "Algebra.Monoid.Solver", name = "Data.replace-consistent")  private CoreFunctionDefinition replaceDef;

  public AlgebraSolverMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false };
  }

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    if (arguments.isEmpty()) {
      return null;
    }
    List<? extends ConcreteExpression> expressions = Utils.getArgumentList(arguments.get(0).getExpression());
    if (expressions.isEmpty()) {
      return null;
    }

    List<ConcreteLetClause> letClauses = new ArrayList<>();
    letClauses.add(ext.factory.letClause(ext.factory.local("d"), Collections.emptyList(), null, ext.factory.hole()));
    for (ConcreteExpression expression : expressions) {
      letClauses.add(ext.factory.letClause(ext.factory.local("r"), Collections.emptyList(), null, expression));
    }
    return ext.factory.letExpr(false, letClauses, ext.factory.hole());
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    CoreFunCallExpression equality = Utils.toEquality(contextData.getExpectedType(), typechecker.getErrorReporter(), contextData.getReferenceExpression());
    if (equality == null) {
      return null;
    }

    CoreClassDefinition classDef = getClassDef(equality.getDefCallArguments().get(0));
    if (classDef == null) {
      typechecker.getErrorReporter().report(new TypeMismatchError(DocFactory.text("Expected a monoid"), equality.getDefCallArguments().get(0), contextData.getReferenceExpression()));
      return null;
    }

    State state = new State(typechecker, contextData.getReferenceExpression(), ext.factory.withData(contextData.getReferenceExpression()));
    ConcreteExpression expr = solve(state, classDef, compileTerm(state, equality.getDefCallArguments().get(1)), compileTerm(state, equality.getDefCallArguments().get(2)), contextData.getArguments().isEmpty() ? null : contextData.getArguments().get(0).getExpression());
    return expr == null ? null : finalizeState(state, expr);
  }

  public CoreClassDefinition getClassDef(CoreExpression type) {
    type = type.normalize(NormalizationMode.WHNF);
    if (type instanceof CoreFieldCallExpression) {
      if (((CoreFieldCallExpression) type).getDefinition() == carrier) {
        CoreExpression instanceType = ((CoreFieldCallExpression) type).getArgument().computeType().normalize(NormalizationMode.WHNF);
        if (instanceType instanceof CoreClassCallExpression) {
          CoreClassDefinition classDef = ((CoreClassCallExpression) instanceType).getDefinition();
          if (classDef.isSubClassOf(monoid)) {
            return classDef;
          }
        }
      }
    }

    return null;
  }

  public static class State {
    public ExpressionTypechecker typechecker;
    public final ConcreteReferenceExpression refExpr;
    public final ConcreteFactory factory;

    public final List<CoreExpression> values = new ArrayList<>();
    public Map<CoreBinding, List<RuleExt>> contextRules = null;

    public final ArendRef dataRef;
    public final List<ConcreteLetClause> letClauses = new ArrayList<>();

    public State(ExpressionTypechecker typechecker, ConcreteReferenceExpression refExpr, ConcreteFactory factory) {
      this.typechecker = typechecker;
      this.refExpr = refExpr;
      this.factory = factory;

      dataRef = factory.local("d");
      letClauses.add(null);
    }

    public State withTypechecker(ExpressionTypechecker typechecker) {
      this.typechecker = typechecker;
      return this;
    }
  }

  public ConcreteExpression solve(State state, CoreClassDefinition classDef, CompiledTerm term1, CompiledTerm term2, ConcreteExpression argument) {
    ErrorReporter errorReporter = state.typechecker.getErrorReporter();
    ConcreteFactory factory = state.factory;

    ConcreteExpression lastArgument;
    if (!term1.nf.equals(term2.nf)) {
      List<RuleExt> rules = new ArrayList<>();
      if (argument == null) {
        if (state.contextRules == null) {
          state.contextRules = new HashMap<>();
        }
        for (CoreBinding binding : state.typechecker.getFreeBindingsList()) {
          rules.addAll(state.contextRules.computeIfAbsent(binding, k -> {
            List<RuleExt> ctxList = new ArrayList<>();
            typeToRule(state, null, binding, ctxList);
            return ctxList;
          }));
        }
      } else {
        for (ConcreteExpression expression : Utils.getArgumentList(argument)) {
          TypedExpression typed = state.typechecker.typecheck(expression, null);
          if (typed == null) {
            return null;
          }
          if (!typeToRule(state, typed, null, rules)) {
            errorReporter.report(new TypeMismatchError(DocFactory.text("algebraic equality"), typed.getType(), expression));
            return null;
          }
        }
      }

      List<Step> trace1 = new ArrayList<>();
      List<Step> trace2 = new ArrayList<>();
      List<Integer> newNf1 = applyRules(term1.nf, rules, trace1);
      List<Integer> newNf2 = applyRules(term2.nf, rules, trace2);
      if (!newNf1.equals(newNf2)) {
        errorReporter.report(new AlgebraSolverError(term1.nf, term2.nf, state.values, rules, trace1, trace2, state.refExpr));
        return null;
      }

      while (!trace1.isEmpty() && !trace2.isEmpty()) {
        if (trace1.get(trace1.size() - 1).equals(trace2.get(trace2.size() - 1))) {
          trace1.remove(trace1.size() - 1);
          trace2.remove(trace2.size() - 1);
        } else {
          break;
        }
      }

      for (Step step : trace1) {
        step.rule.count++;
      }
      for (Step step : trace2) {
        step.rule.count++;
      }
      for (RuleExt rule : rules) {
        if (rule.count > 0) {
          if (rule.rnfTerm == null) {
            rule.rnfTerm = computeNFTerm(rule.rhs, factory);
          }
          if (rule.cExpr != null) {
            continue;
          }

          ConcreteExpression cExpr = rule.binding != null ? factory.ref(rule.binding) : factory.core(null, rule.expression);
          if (rule.direction == Direction.BACKWARD) {
            cExpr = factory.app(factory.ref(ext.inv.getRef()), true, singletonList(cExpr));
          }
          if (!isNF(rule.lhsTerm) || !isNF(rule.rhsTerm)) {
            cExpr = factory.appBuilder(factory.ref(termsEqConv.getRef()))
              .app(factory.ref(state.dataRef), false)
              .app(rule.lhsTerm)
              .app(rule.rhsTerm)
              .app(cExpr)
              .build();
          }
          if (rule.count > 1 && !(cExpr instanceof ConcreteReferenceExpression) || rule.binding == null) {
            ArendRef letClause = factory.local("rule" + state.letClauses.size());
            state.letClauses.add(factory.letClause(letClause, Collections.emptyList(), null, cExpr));
            rule.cExpr = factory.ref(letClause);
          } else {
            rule.cExpr = cExpr;
          }
        }
      }

      ConcreteExpression expr1 = trace1.isEmpty() ? null : traceToExpr(term1.nf, trace1, state.dataRef, factory);
      ConcreteExpression expr2 = trace2.isEmpty() ? null : factory.app(factory.ref(ext.inv.getRef()), true, singletonList(traceToExpr(term2.nf, trace2, state.dataRef, factory)));
      if (expr1 == null && expr2 == null) {
        lastArgument = factory.ref(ext.prelude.getIdp().getRef());
      } else if (expr2 == null) {
        lastArgument = expr1;
      } else if (expr1 == null) {
        lastArgument = expr2;
      } else {
        lastArgument = factory.appBuilder(factory.ref(ext.concat.getRef())).app(expr1).app(expr2).build();
      }
    } else {
      if (argument != null) {
        errorReporter.report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Argument is ignored", argument));
      }
      lastArgument = factory.ref(ext.prelude.getIdp().getRef());
    }

    return factory.appBuilder(factory.ref(termsEq.getRef()))
      .app(factory.ref(state.dataRef), false)
      .app(term1.concrete)
      .app(term2.concrete)
      .app(lastArgument)
      .build();
  }

  public TypedExpression finalizeState(State state, ConcreteExpression expression) {
    ConcreteFactory factory = state.factory;
    ArendRef lamParam = factory.local("n");
    ConcreteClause[] caseClauses = new ConcreteClause[state.values.size() + 1];
    for (int i = 0; i < state.values.size(); i++) {
      caseClauses[i] = factory.clause(singletonList(factory.numberPattern(i)), factory.core(null, state.values.get(i).computeTyped()));
    }
    caseClauses[state.values.size()] = factory.clause(singletonList(factory.refPattern(null, null)), factory.ref(ide.getRef()));

    state.letClauses.set(0, factory.letClause(state.dataRef, Collections.emptyList(), null, factory.newExpr(factory.app(
        factory.ref(dataClass.getRef()), true,
        singletonList(factory.lam(singletonList(factory.param(singletonList(lamParam), factory.ref(ext.prelude.getNat().getRef()))),
                                  factory.caseExpr(false, singletonList(factory.caseArg(factory.ref(lamParam), null, null)), null, null, caseClauses)))))));
    return state.typechecker.typecheck(ext.factory.letExpr(false, state.letClauses, expression), null);
  }

  public enum Direction { FORWARD, BACKWARD, UNKNOWN }

  public static class Rule {
    public final TypedExpression expression;
    public final CoreBinding binding;
    public Direction direction;
    public List<Integer> lhs;
    public List<Integer> rhs;

    public Rule(TypedExpression expression, CoreBinding binding, Direction direction, List<Integer> lhs, List<Integer> rhs) {
      this.expression = expression;
      this.binding = binding;
      this.direction = direction;
      this.lhs = lhs;
      this.rhs = rhs;
    }

    public boolean isIncreasing() {
      return direction == Direction.UNKNOWN ? lhs.size() == rhs.size() : lhs.size() <= rhs.size();
    }
  }

  private static class RuleExt extends Rule {
    private ConcreteExpression lhsTerm;
    private ConcreteExpression rhsTerm;
    private int count;
    private ConcreteExpression cExpr;
    private ConcreteExpression rnfTerm;

    private RuleExt(TypedExpression expression, CoreBinding binding, Direction direction, List<Integer> lhs, List<Integer> rhs, ConcreteExpression lhsTerm, ConcreteExpression rhsTerm) {
      super(expression, binding, direction, lhs, rhs);
      this.lhsTerm = lhsTerm;
      this.rhsTerm = rhsTerm;
    }

    private void setBackward() {
      if (direction == Direction.BACKWARD) {
        return;
      }
      direction = Direction.BACKWARD;
      List<Integer> nf = rhs;
      rhs = lhs;
      lhs = nf;
      ConcreteExpression term = rhsTerm;
      rhsTerm = lhsTerm;
      lhsTerm = term;
    }
  }

  public static class Step {
    public final RuleExt rule;
    public final int position;

    public Step(RuleExt rule, int position) {
      this.rule = rule;
      this.position = position;
    }

    public List<Integer> apply(List<Integer> term) {
      if (term.size() < position + rule.lhs.size()) {
        return null;
      }
      List<Integer> result = new ArrayList<>(term.size() - rule.lhs.size() + rule.rhs.size());
      for (int i = 0; i < position; i++) {
        result.add(term.get(i));
      }
      result.addAll(rule.rhs);
      for (int i = position + rule.lhs.size(); i < term.size(); i++) {
        result.add(term.get(i));
      }
      return result;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      Step step = (Step) o;
      return position == step.position && rule.equals(step.rule);
    }

    @Override
    public int hashCode() {
      return Objects.hash(rule, position);
    }
  }

  private boolean typeToRule(State state, TypedExpression typed, CoreBinding binding, List<RuleExt> rules) {
    if (binding == null && typed == null) {
      return false;
    }
    CoreExpression type = binding != null ? binding.getTypeExpr() : typed.getType();
    CoreFunCallExpression eq = Utils.toEquality(type, null, null);
    if (eq == null) {
      CoreExpression typeNorm = type.normalize(NormalizationMode.WHNF).getUnderlyingExpression();
      if (!(typeNorm instanceof CoreClassCallExpression)) {
        return false;
      }
      CoreClassCallExpression classCall = (CoreClassCallExpression) typeNorm;
      boolean isLDiv = classCall.getDefinition().isSubClassOf(ldiv);
      boolean isRDiv = classCall.getDefinition().isSubClassOf(rdiv);
      if (!isLDiv && !isRDiv) {
        return false;
      }
      List<ConcreteExpression> args = singletonList(binding != null ? state.factory.ref(binding) : state.factory.core(null, typed));
      return (!isLDiv || typeToRule(state, state.typechecker.typecheck(state.factory.app(state.factory.ref(ldiv.getPersonalFields().get(0).getRef()), false, args), null), null, rules)) &&
             (!isRDiv || typeToRule(state, state.typechecker.typecheck(state.factory.app(state.factory.ref(rdiv.getPersonalFields().get(0).getRef()), false, args), null), null, rules));
    }

    List<Integer> lhs = new ArrayList<>();
    List<Integer> rhs = new ArrayList<>();
    ConcreteExpression lhsTerm = computeTerm(state, eq.getDefCallArguments().get(1), lhs);
    ConcreteExpression rhsTerm = computeTerm(state, eq.getDefCallArguments().get(2), rhs);
    if (binding == null) {
      rules.add(new RuleExt(typed, null, Direction.FORWARD, lhs, rhs, lhsTerm, rhsTerm));
    } else {
      Direction direction = lhs.size() > rhs.size() ? Direction.FORWARD : Direction.UNKNOWN;
      RuleExt rule = new RuleExt(typed, binding, direction, lhs, rhs, lhsTerm, rhsTerm);
      if (lhs.size() < rhs.size()) {
        rule.setBackward();
      }
      rules.add(rule);
    }
    return true;
  }

  private static final int MAX_STEPS = 100;

  private List<Integer> applyRules(List<Integer> term, List<RuleExt> rules, List<Step> trace) {
    boolean hasBadRules = false;
    for (RuleExt rule : rules) {
      if (rule.isIncreasing()) {
        hasBadRules = true;
        break;
      }
    }

    int i = 0;
    boolean found;
    do {
      found = false;
      for (RuleExt rule : rules) {
        int pos = Collections.indexOfSubList(term, rule.lhs);
        if (rule.direction == Direction.UNKNOWN) {
          if (pos < 0) {
            pos = Collections.indexOfSubList(term, rule.rhs);
            if (pos >= 0) {
              rule.setBackward();
            }
          } else {
            rule.direction = Direction.FORWARD;
          }
          if (rule.isIncreasing()) {
            hasBadRules = true;
          }
        }
        if (pos >= 0) {
          Step step = new Step(rule, pos);
          trace.add(step);
          term = step.apply(term);
          found = true;
          break;
        }
      }
      i++;
    } while (found && (!hasBadRules || i < MAX_STEPS));

    return term;
  }

  private ConcreteExpression traceToExpr(List<Integer> nf, List<Step> trace, ArendRef dataRef, ConcreteFactory factory) {
    ConcreteExpression result = null;
    for (Step step : trace) {
      ConcreteExpression expr = factory.appBuilder(factory.ref(replaceDef.getRef()))
        .app(factory.ref(dataRef), false)
        .app(computeNFTerm(nf, factory))
        .app(factory.number(step.position))
        .app(factory.number(step.rule.lhs.size()))
        .app(step.rule.rnfTerm)
        .app(step.rule.cExpr)
        .build();
      if (result == null) {
        result = expr;
      } else {
        result = factory.app(factory.ref(ext.concat.getRef()), true, Arrays.asList(result, expr));
      }
      nf = step.apply(nf);
    }
    return result;
  }

  private static boolean isNF(ConcreteExpression term) {
    return term instanceof ConcreteReferenceExpression || isNFRec(term);
  }

  private static boolean isNFRec(ConcreteExpression term) {
    if (!(term instanceof ConcreteAppExpression)) {
      return false;
    }
    List<? extends ConcreteArgument> args = ((ConcreteAppExpression) term).getArguments();
    return args.size() == 1 || args.size() == 2 && args.get(0).getExpression() instanceof ConcreteAppExpression && ((ConcreteAppExpression) args.get(0).getExpression()).getArguments().size() == 1 && isNF(args.get(1).getExpression());
  }

  private ConcreteExpression computeNFTerm(List<Integer> nf, ConcreteFactory factory) {
    ConcreteExpression result = factory.ref(ext.nil.getRef());
    for (int i = nf.size() - 1; i >= 0; i--) {
      result = factory.appBuilder(factory.ref(ext.cons.getRef())).app(factory.number(nf.get(i))).app(result).build();
    }
    return result;
  }

  public static class CompiledTerm {
    public final ConcreteExpression concrete;
    public final List<Integer> nf;

    public CompiledTerm(ConcreteExpression concrete, List<Integer> nf) {
      this.concrete = concrete;
      this.nf = nf;
    }
  }

  public CompiledTerm compileTerm(State state, CoreExpression expression) {
    List<Integer> nf = new ArrayList<>();
    return new CompiledTerm(computeTerm(state, expression, nf), nf);
  }

  private ConcreteExpression computeTerm(State state, CoreExpression expression, List<Integer> nf) {
    expression = expression.normalize(NormalizationMode.WHNF).getUnderlyingExpression();
    if (expression instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) expression).getDefinition() == ide) {
      return state.factory.ref(ideTerm.getRef());
    }

    List<CoreExpression> args = new ArrayList<>(2);
    CoreExpression function = Utils.getAppArguments(expression, 2, args);
    if (args.size() == 2) {
      function = function.normalize(NormalizationMode.WHNF).getUnderlyingExpression();
      if (function instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) function).getDefinition() == mul) {
        List<ConcreteExpression> cArgs = new ArrayList<>(2);
        cArgs.add(computeTerm(state, args.get(0), nf));
        cArgs.add(computeTerm(state, args.get(1), nf));
        return state.factory.app(state.factory.ref(mulTerm.getRef()), true, cArgs);
      }
    }

    int index = state.values.size();
    for (int i = 0; i < state.values.size(); i++) {
      if (state.typechecker.compare(expression, state.values.get(i), CMP.EQ, state.refExpr, false, true)) {
        index = i;
        break;
      }
    }

    if (index == state.values.size()) {
      state.values.add(expression);
    }

    nf.add(index);
    return state.factory.app(state.factory.ref(varTerm.getRef()), true, singletonList(state.factory.number(index)));
  }
}
