package org.arend.lib.meta;

import org.arend.ext.RawDefinitionProvider;
import org.arend.ext.concrete.ConcreteAppBuilder;
import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteLetClause;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFieldCallExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.TypeMismatchError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.module.ModulePath;
import org.arend.ext.prettyprinting.doc.DocFactory;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.RawScope;
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

  public CoreClassField carrier;
  public CoreClassField ide;
  public CoreClassField mul;

  private CoreConstructor varTerm;
  private CoreConstructor ideTerm;
  private CoreConstructor mulTerm;

  private CoreClassDefinition dataClass;
  private CoreFunctionDefinition termsEq;
  private CoreFunctionDefinition termsEqConv;
  private CoreFunctionDefinition replaceDef;

  public AlgebraSolverMeta(StdExtension ext) {
    this.ext = ext;
  }

  public void load(RawDefinitionProvider provider) {
    carrier = provider.getDefinition(ext.moduleScopeProvider.forModule(new ModulePath("Set")).resolveName("BaseSet"), CoreClassDefinition.class).getPersonalFields().get(0);
    ide = provider.getDefinition(ext.moduleScopeProvider.forModule(ModulePath.fromString("Algebra.Pointed")).resolveName("Pointed"), CoreClassDefinition.class).getPersonalFields().get(0);

    mul = provider.getDefinition(ext.moduleScopeProvider.forModule(ModulePath.fromString("Algebra.Monoid")).resolveName("Monoid"), CoreClassDefinition.class).getPersonalFields().get(0);
    RawScope solverScope = ext.moduleScopeProvider.forModule(ModulePath.fromString("Algebra.Monoid.Solver"));
    CoreDataDefinition term = provider.getDefinition(solverScope.resolveName("MonoidTerm"), CoreDataDefinition.class);
    varTerm = term.getConstructors().get(0);
    ideTerm = term.getConstructors().get(1);
    mulTerm = term.getConstructors().get(2);
    dataClass = provider.getDefinition(solverScope.resolveName("Data"), CoreClassDefinition.class);
    RawScope dataScope = solverScope.getSubscope("Data");
    termsEq = provider.getDefinition(dataScope.resolveName("terms-equality"), CoreFunctionDefinition.class);
    termsEqConv = provider.getDefinition(dataScope.resolveName("terms-equality-conv"), CoreFunctionDefinition.class);
    replaceDef = provider.getDefinition(dataScope.resolveName("replace-consistent"), CoreFunctionDefinition.class);
  }

  @Override
  protected @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false };
  }

  @Override
  protected boolean requireExpectedType() {
    return true;
  }

  @Override
  public @Nullable TypedExpression invoke(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    CoreFunCallExpression equality = Utils.toEquality(contextData.getExpectedType(), errorReporter, refExpr);
    if (equality == null) {
      return null;
    }

    CoreExpression instance = null;
    CoreExpression type = equality.getDefCallArguments().get(0).normalize(NormalizationMode.WHNF).getUnderlyingExpression();
    if (type instanceof CoreFieldCallExpression) {
      if (((CoreFieldCallExpression) type).getDefinition() == carrier) {
        instance = ((CoreFieldCallExpression) type).getArgument();
      }
    }
    if (instance == null) {
      errorReporter.report(new TypeMismatchError(DocFactory.text("Expected an equality in a monoid"), equality, refExpr));
      return null;
    }

    List<CoreExpression> values = new ArrayList<>();
    List<Integer> nf1 = new ArrayList<>();
    List<Integer> nf2 = new ArrayList<>();
    ConcreteExpression term1 = computeTerm(equality.getDefCallArguments().get(1), values, typechecker, refExpr, factory, nf1);
    ConcreteExpression term2 = computeTerm(equality.getDefCallArguments().get(2), values, typechecker, refExpr, factory, nf2);

    List<ConcreteLetClause> letClauses = new ArrayList<>();
    letClauses.add(null);
    ArendRef dataRef = factory.local("d");
    ConcreteExpression lastArgument;
    if (!nf1.equals(nf2)) {
      List<RuleExt> rules;
      if (contextData.getArguments().isEmpty()) {
        rules = Collections.emptyList();
      } else {
        List<? extends ConcreteExpression> expressions;
        ConcreteExpression arg = contextData.getArguments().get(0).getExpression();
        if (arg instanceof ConcreteTupleExpression) {
          expressions = ((ConcreteTupleExpression) arg).getFields();
        } else {
          expressions = singletonList(arg);
        }

        rules = new ArrayList<>();
        for (ConcreteExpression expression : expressions) {
          TypedExpression typed = typechecker.typecheck(expression, null);
          if (typed == null) {
            return null;
          }
          CoreFunCallExpression eq = Utils.toEquality(typed.getType(), errorReporter, expression);
          if (eq == null) {
            return null;
          }

          List<Integer> lhs = new ArrayList<>();
          List<Integer> rhs = new ArrayList<>();
          ConcreteExpression lhsTerm = computeTerm(eq.getDefCallArguments().get(1), values, typechecker, refExpr, factory, lhs);
          ConcreteExpression rhsTerm = computeTerm(eq.getDefCallArguments().get(2), values, typechecker, refExpr, factory, rhs);
          rules.add(new RuleExt(typed, null, false, lhs, rhs, lhsTerm, rhsTerm));
        }
      }

      List<Step> trace1 = new ArrayList<>();
      List<Step> trace2 = new ArrayList<>();
      List<Integer> newNf1 = applyRules(nf1, rules, trace1);
      List<Integer> newNf2 = applyRules(nf2, rules, trace2);
      if (!newNf1.equals(newNf2)) {
        errorReporter.report(new AlgebraSolverError(nf1, nf2, values, rules, trace1, trace2, refExpr));
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
      int letNum = 1;
      for (RuleExt rule : rules) {
        if (rule.count > 0) {
          rule.rnfTerm = computeNFTerm(rule.rhs, factory);

          ConcreteExpression cExpr = rule.reference != null ? factory.ref(rule.reference) : factory.core("rule", rule.expression);
          if (rule.isInverted) {
            cExpr = factory.app(factory.ref(ext.inv.getRef()), true, singletonList(cExpr));
          }
          if (!isNF(rule.lhsTerm) || !isNF(rule.rhsTerm)) {
            cExpr = factory.appBuilder(factory.ref(termsEqConv.getRef()))
              .app(factory.ref(dataRef), false)
              .app(rule.lhsTerm)
              .app(rule.rhsTerm)
              .app(cExpr)
              .build();
          }
          if (rule.count > 1 && !(cExpr instanceof ConcreteReferenceExpression)) {
            ArendRef letClause = factory.local("rule" + letNum++);
            letClauses.add(factory.letClause(letClause, Collections.emptyList(), null, cExpr));
            rule.cExpr = factory.ref(letClause);
          } else {
            rule.cExpr = cExpr;
          }
        }
      }

      ConcreteExpression expr1 = trace1.isEmpty() ? null : traceToExpr(nf1, trace1, false, dataRef, factory);
      ConcreteExpression expr2 = trace2.isEmpty() ? null : factory.app(factory.ref(ext.inv.getRef()), true, singletonList(traceToExpr(nf2, trace2, true, dataRef, factory)));
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
      if (!contextData.getArguments().isEmpty()) {
        errorReporter.report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Argument is ignored", contextData.getArguments().get(0).getExpression()));
      }
      lastArgument = factory.ref(ext.prelude.getIdp().getRef());
    }

    ArendRef lamParam = factory.local("n");
    ConcreteClause[] caseClauses = new ConcreteClause[values.size() + 1];
    for (int i = 0; i < values.size(); i++) {
      caseClauses[i] = factory.clause(singletonList(factory.numberPattern(i)), factory.core("c" + i, values.get(i).computeTyped()));
    }
    caseClauses[values.size()] = factory.clause(singletonList(factory.refPattern(null, null)), factory.ref(ide.getRef()));

    letClauses.set(0, factory.letClause(dataRef, Collections.emptyList(), null, factory.newExpr(factory.app(
      factory.ref(dataClass.getRef()), true,
      singletonList(factory.lam(singletonList(factory.param(singletonList(lamParam), factory.ref(ext.prelude.getNat().getRef()))),
                                factory.caseExpr(false, singletonList(factory.caseArg(factory.ref(lamParam), null, null)), null, null, caseClauses)))))));
    return typechecker.typecheck(ext.factory.letExpr(false, letClauses, factory.appBuilder(factory.ref(termsEq.getRef()))
      .app(factory.ref(dataRef), false)
      .app(term1)
      .app(term2)
      .app(lastArgument)
      .build()), null);
  }

  public static class Rule {
    public final TypedExpression expression;
    public final ArendRef reference;
    public final boolean isInverted;
    public final List<Integer> lhs;
    public final List<Integer> rhs;

    public Rule(TypedExpression expression, ArendRef reference, boolean isInverted, List<Integer> lhs, List<Integer> rhs) {
      this.expression = expression;
      this.reference = reference;
      this.isInverted = isInverted;
      this.lhs = lhs;
      this.rhs = rhs;
    }
  }

  private static class RuleExt extends Rule {
    private final ConcreteExpression lhsTerm;
    private final ConcreteExpression rhsTerm;
    private int count;
    private ConcreteExpression cExpr;
    private ConcreteExpression rnfTerm;

    private RuleExt(TypedExpression expression, ArendRef reference, boolean isInversed, List<Integer> lhs, List<Integer> rhs, ConcreteExpression lhsTerm, ConcreteExpression rhsTerm) {
      super(expression, reference, isInversed, lhs, rhs);
      this.lhsTerm = lhsTerm;
      this.rhsTerm = rhsTerm;
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

  private List<Integer> applyRules(List<Integer> term, List<RuleExt> rules, List<Step> trace) {
    boolean found;
    do {
      found = false;
      for (RuleExt rule : rules) {
        int pos = Collections.indexOfSubList(term, rule.lhs);
        if (pos >= 0) {
          Step step = new Step(rule, pos);
          trace.add(step);
          term = step.apply(term);
          found = true;
          break;
        }
      }
    } while (found);

    return term;
  }

  private ConcreteExpression traceToExpr(List<Integer> nf, List<Step> trace, boolean isReversed, ArendRef dataRef, ConcreteFactory factory) {
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
        ConcreteAppBuilder builder = factory.appBuilder(factory.ref(ext.concat.getRef()));
        if (isReversed) {
          builder.app(expr).app(result);
        } else {
          builder.app(result).app(expr);
        }
        result = builder.build();
      }
      nf = step.apply(nf);
    }
    return result;
  }

  private boolean isNF(ConcreteExpression term) {
    if (term instanceof ConcreteReferenceExpression) {
      return true;
    }
    if (!(term instanceof ConcreteAppExpression)) {
      return false;
    }
    List<? extends ConcreteArgument> args = ((ConcreteAppExpression) term).getArguments();
    return args.size() == 2 && args.get(0).getExpression() instanceof ConcreteReferenceExpression && isNF(args.get(1).getExpression());
  }

  private ConcreteExpression computeNFTerm(List<Integer> nf, ConcreteFactory factory) {
    ConcreteExpression result = factory.ref(ext.nil.getRef());
    for (int i = nf.size() - 1; i >= 0; i--) {
      result = factory.appBuilder(factory.ref(ext.cons.getRef())).app(factory.number(nf.get(i))).app(result).build();
    }
    return result;
  }

  private ConcreteExpression computeTerm(CoreExpression expression, List<CoreExpression> values, ExpressionTypechecker typechecker, ConcreteReferenceExpression marker, ConcreteFactory factory, List<Integer> nf) {
    expression = expression.normalize(NormalizationMode.WHNF).getUnderlyingExpression();
    if (expression instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) expression).getDefinition() == ide) {
      return factory.ref(ideTerm.getRef());
    }

    List<CoreExpression> args = new ArrayList<>(2);
    CoreExpression function = Utils.getAppArguments(expression, 2, args);
    if (args.size() == 2) {
      function = function.normalize(NormalizationMode.WHNF).getUnderlyingExpression();
      if (function instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) function).getDefinition() == mul) {
        List<ConcreteExpression> cArgs = new ArrayList<>(2);
        cArgs.add(computeTerm(args.get(0), values, typechecker, marker, factory, nf));
        cArgs.add(computeTerm(args.get(1), values, typechecker, marker, factory, nf));
        return factory.app(factory.ref(mulTerm.getRef()), true, cArgs);
      }
    }

    int index = values.size();
    for (int i = 0; i < values.size(); i++) {
      if (typechecker.compare(expression, values.get(i), CMP.EQ, marker, false, true)) {
        index = i;
        break;
      }
    }

    if (index == values.size()) {
      values.add(expression);
    }

    nf.add(index);
    return factory.app(factory.ref(varTerm.getRef()), true, singletonList(factory.number(index)));
  }
}
