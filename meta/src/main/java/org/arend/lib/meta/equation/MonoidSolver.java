package org.arend.lib.meta.equation;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.expr.ConcreteAppExpression;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.context.ContextHelper;
import org.arend.lib.error.AlgebraSolverError;
import org.arend.lib.util.Maybe;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

import static java.util.Collections.singletonList;

public class MonoidSolver implements EquationSolver {
  private final EquationMeta meta;
  private final ExpressionTypechecker typechecker;
  private final ConcreteFactory factory;
  private final ConcreteReferenceExpression refExpr;

  private final BinOpMatcher binOpMatcher;
  private final CoreExpression ideExpr;
  private final Values<CoreExpression> values;
  private CompiledTerm lastCompiled;
  private TypedExpression lastTerm;
  private final ArendRef dataRef;
  private final List<ConcreteLetClause> letClauses;
  private Map<CoreBinding, List<RuleExt>> contextRules;
  private final CoreFunCallExpression equality;

  public MonoidSolver(EquationMeta meta, ExpressionTypechecker typechecker, ConcreteFactory factory, ConcreteReferenceExpression refExpr, CoreFunCallExpression equality, TypedExpression instance, CoreClassCallExpression classCall) {
    this.meta = meta;
    this.typechecker = typechecker;
    this.factory = factory;
    this.refExpr = refExpr;
    this.equality = equality;
    ideExpr = classCall.getImplementation(meta.ide, instance);
    CoreExpression mulExpr = classCall.getImplementation(meta.mul, instance);
    TypedExpression mulTyped = mulExpr == null ? null : mulExpr.computeTyped();

    BinOpMatcher matcher = null;
    if (mulTyped != null) {
      CoreExpression expr = mulTyped.getExpression();
      if (expr instanceof CoreLamExpression) {
        CoreExpression body = ((CoreLamExpression) expr).getBody();
        CoreParameter param1 = ((CoreLamExpression) expr).getParameters();
        CoreParameter param2 = param1.getNext();
        if (!param2.hasNext() && body instanceof CoreLamExpression) {
          param2 = ((CoreLamExpression) body).getParameters();
          body = ((CoreLamExpression) body).getBody();
        }
        if (param2.hasNext() && !param2.getNext().hasNext() && body instanceof CoreFunCallExpression && ((CoreFunCallExpression) body).getDefinition() == meta.ext.append) {
          List<? extends CoreExpression> args = ((CoreFunCallExpression) body).getDefCallArguments();
          if (args.get(1) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(1)).getBinding() == param1.getBinding() && args.get(2) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(2)).getBinding() == param2.getBinding()) {
            matcher = new ListBinOpMatcher();
          }
        }
        if (matcher == null) {
          matcher = new GeneralBinOpMatcher(mulTyped, ((CoreLamExpression) expr).getParameters().getTypeExpr());
        }
      }
    }
    binOpMatcher = matcher;

    values = new Values<>(typechecker, refExpr);
    dataRef = factory.local("d");
    letClauses = new ArrayList<>();
    letClauses.add(null);
  }

  private interface BinOpMatcher {
    void match(CoreExpression expr, List<CoreExpression> args);
  }

  private class GeneralBinOpMatcher implements BinOpMatcher {
    private final TypedExpression mulTyped;
    private final CoreExpression carrierExpr;

    private GeneralBinOpMatcher(TypedExpression mulTyped, CoreExpression carrierExpr) {
      this.mulTyped = mulTyped;
      this.carrierExpr = carrierExpr;
    }

    @Override
    public void match(CoreExpression expr, List<CoreExpression> args) {
      typechecker.withCurrentState(tc -> {
        CoreInferenceReferenceExpression varExpr1 = typechecker.generateNewInferenceVariable("var1", carrierExpr, refExpr, true);
        CoreInferenceReferenceExpression varExpr2 = typechecker.generateNewInferenceVariable("var2", carrierExpr, refExpr, true);
        TypedExpression result = tc.typecheck(factory.app(factory.core(mulTyped), true, Arrays.asList(factory.core(varExpr1.computeTyped()), factory.core(varExpr2.computeTyped()))), null);
        if (result != null && tc.compare(result.getExpression(), expr, CMP.EQ, refExpr, false, true) && varExpr1.getSubstExpression() != null && varExpr2.getSubstExpression() != null) {
          args.add(varExpr1.getSubstExpression());
          args.add(varExpr2.getSubstExpression());
        } else {
          tc.loadSavedState();
        }
        return null;
      });
    }
  }

  private class ListBinOpMatcher implements BinOpMatcher {
    @Override
    public void match(CoreExpression expr, List<CoreExpression> args) {
      if (expr instanceof CoreFunCallExpression && ((CoreFunCallExpression) expr).getDefinition() == meta.ext.append) {
        List<? extends CoreExpression> defCallArgs = ((CoreFunCallExpression) expr).getDefCallArguments();
        args.add(defCallArgs.get(1));
        args.add(defCallArgs.get(2));
      } else if (expr instanceof CoreConCallExpression && ((CoreConCallExpression) expr).getDefinition() == meta.ext.cons) {
        List<? extends CoreExpression> defCallArgs = ((CoreConCallExpression) expr).getDefCallArguments();
        CoreExpression tail = defCallArgs.get(1).normalize(NormalizationMode.WHNF);
        if (!(tail instanceof CoreConCallExpression && ((CoreConCallExpression) tail).getDefinition() == meta.ext.nil)) {
          TypedExpression result = typechecker.typecheck(factory.app(factory.ref(meta.ext.cons.getRef()), true, Arrays.asList(factory.core(defCallArgs.get(0).computeTyped()), factory.ref(meta.ext.nil.getRef()))), null);
          if (result != null) {
            args.add(result.getExpression());
            args.add(tail);
          }
        }
      }
    }
  }

  @Override
  public boolean isApplicable(CoreExpression type) {
    return true;
  }

  @Override
  public CoreExpression getValuesType() {
    return equality.getDefCallArguments().get(0);
  }

  @Override
  public CoreExpression getLeftValue() {
    return equality.getDefCallArguments().get(1);
  }

  @Override
  public CoreExpression getRightValue() {
    return equality.getDefCallArguments().get(2);
  }

  @Override
  public @Nullable Maybe<CoreExpression> getEqType(@Nullable TypedExpression leftExpr, @Nullable TypedExpression rightExpr) {
    if (leftExpr != null && rightExpr != null) {
      TypedExpression result = typechecker.typecheck(factory.app(factory.ref(meta.ext.prelude.getEquality().getRef()), true, Arrays.asList(factory.core(null, leftExpr), factory.core(null, rightExpr))), null);
      return result == null ? null : new Maybe<>(result.getExpression());
    } else {
      return new Maybe<>(null);
    }
  }

  @Override
  public TypedExpression getTrivialResult(TypedExpression expression) {
    return typechecker.typecheck(factory.app(factory.ref(meta.ext.prelude.getIdp().getRef()), false, Arrays.asList(factory.hole(), factory.core(null, expression))), null);
  }

  @Override
  public ConcreteExpression combineResults(ConcreteExpression expr1, ConcreteExpression expr2) {
    return factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(expr1, expr2));
  }

  @Override
  public boolean isHint(ConcreteExpression expression) {
    return ContextHelper.getMeta(expression) != null;
  }

  @Override
  public boolean initializeSolver() {
    return true;
  }

  @Override
  public ConcreteExpression solve(@Nullable ConcreteExpression hint, @NotNull TypedExpression leftExpr, @NotNull TypedExpression rightExpr, @NotNull ErrorReporter errorReporter) {
    CompiledTerm term1 = lastTerm == leftExpr ? lastCompiled : compileTerm(leftExpr.getExpression());
    CompiledTerm term2 = compileTerm(rightExpr.getExpression());
    lastTerm = rightExpr;
    lastCompiled = term2;

    ConcreteExpression lastArgument;
    if (!term1.nf.equals(term2.nf)) {
      List<RuleExt> rules = new ArrayList<>();
      if (contextRules == null) {
        contextRules = new HashMap<>();
      }
      ContextHelper helper = new ContextHelper(hint);
      for (CoreBinding binding : helper.getContextBindings(typechecker)) {
        rules.addAll(contextRules.computeIfAbsent(binding, k -> {
          List<RuleExt> ctxList = new ArrayList<>();
          typeToRule(null, binding, false, ctxList);
          return ctxList;
        }));
      }
      for (CoreBinding binding : helper.getAdditionalBindings(typechecker)) {
        typeToRule(null, binding, true, rules);
      }

      List<Step> trace1 = new ArrayList<>();
      List<Step> trace2 = new ArrayList<>();
      List<Integer> newNf1 = applyRules(term1.nf, rules, trace1);
      List<Integer> newNf2 = applyRules(term2.nf, rules, trace2);
      if (!newNf1.equals(newNf2)) {
        errorReporter.report(new AlgebraSolverError(term1.nf, term2.nf, values.getValues(), rules, trace1, trace2, hint != null ? hint : refExpr));
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
            cExpr = factory.app(factory.ref(meta.ext.inv.getRef()), true, singletonList(cExpr));
          }
          if (!isNF(rule.lhsTerm) || !isNF(rule.rhsTerm)) {
            cExpr = factory.appBuilder(factory.ref(meta.termsEqConv.getRef()))
              .app(factory.ref(dataRef), false)
              .app(rule.lhsTerm)
              .app(rule.rhsTerm)
              .app(cExpr)
              .build();
          }
          if (rule.count > 1 && !(cExpr instanceof ConcreteReferenceExpression) || rule.binding == null) {
            ArendRef letClause = factory.local("rule" + letClauses.size());
            letClauses.add(factory.letClause(letClause, Collections.emptyList(), null, cExpr));
            rule.cExpr = factory.ref(letClause);
          } else {
            rule.cExpr = cExpr;
          }
        }
      }

      ConcreteExpression expr1 = trace1.isEmpty() ? null : traceToExpr(term1.nf, trace1, dataRef, factory);
      ConcreteExpression expr2 = trace2.isEmpty() ? null : factory.app(factory.ref(meta.ext.inv.getRef()), true, singletonList(traceToExpr(term2.nf, trace2, dataRef, factory)));
      if (expr1 == null && expr2 == null) {
        lastArgument = factory.ref(meta.ext.prelude.getIdp().getRef());
      } else if (expr2 == null) {
        lastArgument = expr1;
      } else if (expr1 == null) {
        lastArgument = expr2;
      } else {
        lastArgument = factory.appBuilder(factory.ref(meta.ext.concat.getRef())).app(expr1).app(expr2).build();
      }
    } else {
      lastArgument = factory.ref(meta.ext.prelude.getIdp().getRef());
    }

    return factory.appBuilder(factory.ref(meta.termsEq.getRef()))
      .app(factory.ref(dataRef), false)
      .app(term1.concrete)
      .app(term2.concrete)
      .app(lastArgument)
      .build();
  }

  private boolean typeToRule(TypedExpression typed, CoreBinding binding, boolean alwaysForward, List<RuleExt> rules) {
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
      boolean isLDiv = classCall.getDefinition().isSubClassOf(meta.ldiv);
      boolean isRDiv = classCall.getDefinition().isSubClassOf(meta.rdiv);
      if (!isLDiv && !isRDiv) {
        return false;
      }
      List<ConcreteExpression> args = singletonList(binding != null ? factory.ref(binding) : factory.core(null, typed));
      return (!isLDiv || typeToRule(typechecker.typecheck(factory.app(factory.ref(meta.ldiv.getPersonalFields().get(0).getRef()), false, args), null), null, true, rules)) &&
        (!isRDiv || typeToRule(typechecker.typecheck(factory.app(factory.ref(meta.rdiv.getPersonalFields().get(0).getRef()), false, args), null), null, true, rules));
    }

    List<Integer> lhs = new ArrayList<>();
    List<Integer> rhs = new ArrayList<>();
    ConcreteExpression lhsTerm = computeTerm(eq.getDefCallArguments().get(1), lhs);
    ConcreteExpression rhsTerm = computeTerm(eq.getDefCallArguments().get(2), rhs);
    if (binding == null) {
      rules.add(new RuleExt(typed, null, Direction.FORWARD, lhs, rhs, lhsTerm, rhsTerm));
    } else {
      Direction direction = alwaysForward || lhs.size() > rhs.size() ? Direction.FORWARD : Direction.UNKNOWN;
      RuleExt rule = new RuleExt(typed, binding, direction, lhs, rhs, lhsTerm, rhsTerm);
      if (!alwaysForward && lhs.size() < rhs.size()) {
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
      ConcreteExpression expr = factory.appBuilder(factory.ref(meta.replaceDef.getRef()))
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
        result = factory.app(factory.ref(meta.ext.concat.getRef()), true, Arrays.asList(result, expr));
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
    ConcreteExpression result = factory.ref(meta.ext.nil.getRef());
    for (int i = nf.size() - 1; i >= 0; i--) {
      result = factory.appBuilder(factory.ref(meta.ext.cons.getRef())).app(factory.number(nf.get(i))).app(result).build();
    }
    return result;
  }

  public enum Direction { FORWARD, BACKWARD, UNKNOWN }

  public static class Step {
    private final RuleExt rule;
    private final int position;

    private Step(RuleExt rule, int position) {
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

  public static class Rule {
    public final TypedExpression expression;
    public final CoreBinding binding;
    public Direction direction;
    public List<Integer> lhs;
    public List<Integer> rhs;

    private Rule(TypedExpression expression, CoreBinding binding, Direction direction, List<Integer> lhs, List<Integer> rhs) {
      this.expression = expression;
      this.binding = binding;
      this.direction = direction;
      this.lhs = lhs;
      this.rhs = rhs;
    }

    boolean isIncreasing() {
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

  private static class CompiledTerm {
    private final ConcreteExpression concrete;
    private final List<Integer> nf;

    private CompiledTerm(ConcreteExpression concrete, List<Integer> nf) {
      this.concrete = concrete;
      this.nf = nf;
    }
  }

  private CompiledTerm compileTerm(CoreExpression expression) {
    List<Integer> nf = new ArrayList<>();
    return new CompiledTerm(computeTerm(expression, nf), nf);
  }

  private ConcreteExpression computeTerm(CoreExpression expression, List<Integer> nf) {
    CoreExpression expr = expression.normalize(NormalizationMode.WHNF);

    if (ideExpr == null && expr instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) expr).getDefinition() == meta.ide) {
      return factory.ref(meta.ideTerm.getRef());
    }
    if (ideExpr != null && Utils.safeCompare(typechecker, ideExpr, expr, CMP.EQ, refExpr, false, true)) {
      return factory.ref(meta.ideTerm.getRef());
    }

    List<CoreExpression> args = new ArrayList<>(2);
    if (binOpMatcher == null) {
      CoreExpression function = Utils.getAppArguments(expr, 2, args);
      if (args.size() == 2) {
        function = function.normalize(NormalizationMode.WHNF).getUnderlyingExpression();
        if (!(function instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) function).getDefinition() == meta.mul)) {
          args.clear();
        }
      }
    } else {
      binOpMatcher.match(expr, args);
    }

    if (args.size() == 2) {
      List<ConcreteExpression> cArgs = new ArrayList<>(2);
      cArgs.add(computeTerm(args.get(0), nf));
      cArgs.add(computeTerm(args.get(1), nf));
      return factory.app(factory.ref(meta.mulTerm.getRef()), true, cArgs);
    }

    int index = values.addValue(expr);
    nf.add(index);
    return factory.app(factory.ref(meta.varTerm.getRef()), true, singletonList(factory.number(index)));
  }

  @Override
  public TypedExpression finalize(ConcreteExpression result) {
    ArendRef lamParam = factory.local("n");
    List<CoreExpression> valueList = values.getValues();
    ConcreteClause[] caseClauses = new ConcreteClause[valueList.size() + 1];
    for (int i = 0; i < valueList.size(); i++) {
      caseClauses[i] = factory.clause(singletonList(factory.numberPattern(i)), factory.core(null, valueList.get(i).computeTyped()));
    }
    caseClauses[valueList.size()] = factory.clause(singletonList(factory.refPattern(null, null)), factory.ref(meta.ide.getRef()));

    letClauses.set(0, factory.letClause(dataRef, Collections.emptyList(), null, factory.newExpr(factory.app(
      factory.ref(meta.Data.getRef()), true,
      singletonList(factory.lam(singletonList(factory.param(singletonList(lamParam), factory.ref(meta.ext.prelude.getNat().getRef()))),
        factory.caseExpr(false, singletonList(factory.caseArg(factory.ref(lamParam), null, null)), null, null, caseClauses)))))));
    return typechecker.typecheck(meta.ext.factory.letExpr(false, letClauses, result), null);
  }
}
