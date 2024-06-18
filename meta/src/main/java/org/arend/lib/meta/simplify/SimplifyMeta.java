package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.instance.InstanceSearchParameters;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.ext.util.Wrapper;
import org.arend.lib.StdExtension;
import org.arend.lib.error.SimplifyError;
import org.arend.lib.error.TypeError;
import org.arend.lib.meta.RewriteMeta;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

public class SimplifyMeta extends BaseMetaDefinition {
  private final StdExtension ext;
  private ExpressionTypechecker typechecker;
  private ConcreteReferenceExpression refExpr;
  private ConcreteFactory factory;
  private ErrorReporter errorReporter;

  public SimplifyMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }

  private class SimplifyExpressionProcessor implements Function<CoreExpression, CoreExpression.FindAction> {

    private final List<Pair<CoreExpression, RewriteMeta.EqProofConcrete>> simplificationOccurrences = new ArrayList<>();
    private final Map<Wrapper<CoreExpression>, CoreExpression> exprsToNormalize = new HashMap<>();
    private boolean isFirstLaunch = true;
    private boolean skipRoot = false;

    public List<Pair<CoreExpression, RewriteMeta.EqProofConcrete>> getSimplificationOccurrences() {
      return simplificationOccurrences;
    }

    public Map<Wrapper<CoreExpression>, CoreExpression> getExprsToNormalize() {
      return exprsToNormalize;
    }

    public SimplifyExpressionProcessor() {

    }

    public SimplifyExpressionProcessor(boolean skipRoot) {
      this.skipRoot = skipRoot;
    }

    private final List<CoreParameter> lamParams = new ArrayList<>();

    @Override
    public CoreExpression.FindAction apply(CoreExpression expression) {
      if (skipRoot && isFirstLaunch) {
        isFirstLaunch = false;
        return CoreExpression.FindAction.CONTINUE;
      }

      if (lamParams.stream().anyMatch(p -> expression.findFreeBindings().contains(p.getBinding()))) {
        return CoreExpression.FindAction.CONTINUE;
      }

      var simplificationRules = new TreeSet<SimplificationRule>((o1, o2) -> o1.equals(o2) ? 0 : o1.hashCode() - o2.hashCode()); //getSimplificationRulesForType(expression.computeType());
      var normExpr = expression.normalize(NormalizationMode.ENF);
      var simplifiedExpr = normExpr.computeTyped();

      if (normExpr instanceof CoreLamExpression lam) {
        lamParams.add(lam.getParameters());
      }

      simplificationRules.addAll(getSimplificationRulesForType(expression.computeType()));

    /*  if (simplificationRules.stream().anyMatch(rule -> rule instanceof LocalSimplificationRuleBase)) {
        simplifiedExpr.getExpression().processSubexpression(subexpr -> {
          simplificationRules.addAll(getSimplificationRulesForType(subexpr.computeType()));
          return CoreExpression.FindAction.CONTINUE;
        });
      } /**/

      ConcreteExpression right = null;
      ConcreteExpression path = null;
      // boolean wasSimplified = false;
      boolean keepSimplifying = true;
      while (keepSimplifying) {
        typechecker.checkCancelled();
        keepSimplifying = false;
        for (var rule : simplificationRules) {
          var simplificationRes = rule.apply(simplifiedExpr);
        //  wasSimplified = true;
          if (simplificationRes == null) continue;
          keepSimplifying = true;
          var finalizedEqProof = rule.finalizeEqProof(simplificationRes.proof);
          if (path == null) {
            path = finalizedEqProof;
          } else {
            path = factory.appBuilder(factory.ref(ext.concat.getRef()))
              // .app(factory.hole(), false)
              //.app(factory.core(expression.computeTyped()), false).app(right, false).app(simplificationRes.right, false)
              .app(path).app(finalizedEqProof).build();
          }
          right = simplificationRes.right;
          simplifiedExpr = typechecker.typecheck(simplificationRes.right, simplifiedExpr.getType());
          if (simplifiedExpr == null) {
            isFirstLaunch = false;
            return CoreExpression.FindAction.SKIP;
          }
        }
      }
      if (path == null) {
        /*if (wasSimplified) {
          return CoreExpression.FindAction.SKIP;
        }
        return CoreExpression.FindAction.CONTINUE; /**/
        var processor = new SimplifyExpressionProcessor(true);
        processor.lamParams.addAll(lamParams);
        // var subexpr = normExpr;
        typechecker.withCurrentState(tc -> normExpr.processSubexpression(processor));
        simplificationOccurrences.addAll(processor.getSimplificationOccurrences());
        isFirstLaunch = false;
        if (!processor.getSimplificationOccurrences().isEmpty() && expression != normExpr) {
          exprsToNormalize.put(new Wrapper<>(expression), normExpr);
        }
        exprsToNormalize.putAll(processor.exprsToNormalize);
        return CoreExpression.FindAction.SKIP;
      }
      if (expression != normExpr) {
        exprsToNormalize.put(new Wrapper<>(expression), normExpr);
      }
      isFirstLaunch = false;
      simplificationOccurrences.add(new Pair<>(normExpr, new RewriteMeta.EqProofConcrete(path, factory.core(expression.computeTyped()), right)));
      return CoreExpression.FindAction.SKIP;
    }
  }

  private List<SimplificationRule> getSimplificationRulesForType(CoreExpression type) {
    var rules = new ArrayList<SimplificationRule>();
    type = type == null ? null : type.normalize(NormalizationMode.WHNF);
    var possibleClasses = new HashSet<>(Arrays.asList(ext.equationMeta.Monoid, ext.equationMeta.AddMonoid, ext.equationMeta.Semiring, ext.equationMeta.Ring, ext.equationMeta.AddGroup, ext.equationMeta.Group, ext.equationMeta.CGroup, ext.equationMeta.AbGroup));
    var instanceClassCallPair = Utils.findInstanceWithClassCall(new InstanceSearchParameters() {
      @Override
      public boolean testClass(@NotNull CoreClassDefinition classDefinition) {
        for (var clazz : possibleClasses) {
          if (classDefinition.isSubClassOf(clazz)) {
            return true;
          }
        }
        return false;
      }
    }, ext.carrier, type, typechecker, refExpr, null);
    if (instanceClassCallPair != null) {
      TypedExpression instance = instanceClassCallPair.proj1;
      CoreClassCallExpression classCall = instanceClassCallPair.proj2;
      if (classCall != null) {
        if (classCall.getDefinition().isSubClassOf(ext.equationMeta.Monoid)) {
          rules.add(new MonoidIdentityRule(instance, classCall, ext, refExpr, typechecker, false));
        }
        if (classCall.getDefinition().isSubClassOf(ext.equationMeta.AddMonoid)) {
          rules.add(new MonoidIdentityRule(instance, classCall, ext, refExpr, typechecker, true));
        }
        if (classCall.getDefinition().isSubClassOf(ext.equationMeta.Semiring)) {
          rules.add(new MultiplicationByZeroRule(instance, classCall, ext, refExpr, typechecker));
        }
        if (classCall.getDefinition().isSubClassOf(ext.equationMeta.Ring)) {
          rules.add(new MulOfNegativesRule(instance, classCall, ext, refExpr, typechecker));
        }

        if (classCall.getDefinition().isSubClassOf(ext.equationMeta.AddGroup)) {
          rules.add(new DoubleNegationRule(instance, classCall, ext, refExpr, typechecker, true));
          rules.add(new IdentityInverseRule(instance, classCall, ext, refExpr, typechecker, true));
          rules.add(new NegationPropagationRule(instance, classCall, ext, refExpr, typechecker, true));
        } else if (classCall.getDefinition().isSubClassOf(ext.equationMeta.Group)) {
          rules.add(new DoubleNegationRule(instance, classCall, ext, refExpr, typechecker, false));
          rules.add(new IdentityInverseRule(instance, classCall, ext, refExpr, typechecker, false));
          rules.add(new NegationPropagationRule(instance, classCall, ext, refExpr, typechecker, false));
        }/**/

        if (classCall.getDefinition().isSubClassOf(ext.equationMeta.CGroup)) {
          rules.add(new AbGroupInverseRule(instance, classCall, ext, refExpr, typechecker, false));
        } else if (classCall.getDefinition().isSubClassOf(ext.equationMeta.AbGroup)) {
          rules.add(new AbGroupInverseRule(instance, classCall, ext, refExpr, typechecker, true));
        } else if (classCall.getDefinition().isSubClassOf(ext.equationMeta.Group)) {
          rules.add(new GroupInverseRule(instance, classCall, ext, refExpr, typechecker, false));
        } else if (classCall.getDefinition().isSubClassOf(ext.equationMeta.AddGroup)) {
          rules.add(new GroupInverseRule(instance, classCall, ext, refExpr, typechecker, true));
        }/**/
      }
    }

    return rules;
  }

  private UncheckedExpression replaceSubexpr(CoreExpression expr, List<TypedExpression> checkedVars, Map<Wrapper<CoreExpression>, Integer> indexOfSubExpr, Map<Wrapper<CoreExpression>, CoreExpression> subexprsToNormalize, List<CoreExpression> occurrences) {
    CoreExpression normExpr = subexprsToNormalize.getOrDefault(new Wrapper<>(expr), expr);
    var uncheckedRes = normExpr.replaceSubexpressions(expression -> {
      Integer occurInd = indexOfSubExpr.get(new Wrapper<>(expression));
      if (occurInd == null) {
        if (expression != normExpr && subexprsToNormalize.containsKey(new Wrapper<>(expression))) {
          return replaceSubexpr(expression, checkedVars, indexOfSubExpr, subexprsToNormalize, occurrences);
          // return subExprRes == null ? null : subExprRes.getExpression();
        }
        return null;
      }
      return checkedVars.get(occurInd).getExpression();
    }, true);
    /*TypedExpression result = uncheckedRes != null ? Utils.tryTypecheck(typechecker, tc -> tc.check(uncheckedRes, refExpr)) : null;
    if (result == null) {
      errorReporter.report(new SimplifyError(typechecker.getExpressionPrettifier(), occurrences, normExpr, refExpr));
    } */
    return uncheckedRes;
  }

  private ConcreteExpression simplifyTypeOfExpression(ConcreteExpression expression, CoreExpression type, boolean isForward) {
    CoreExpression normType = type.normalize(NormalizationMode.WHNF);
    var processor = new SimplifyExpressionProcessor();
    typechecker.withCurrentState(tc -> normType.processSubexpression(processor));

    var occurrences = processor.getSimplificationOccurrences().stream().map(x -> x.proj1).collect(Collectors.toList());
    var lamParams = new ArrayList<ConcreteParameter>();

    if (occurrences.isEmpty()) {
      errorReporter.report(new TypecheckingError("Nothing to simplify", refExpr));
      return expression;
    }

    for (int i = 0; i < occurrences.size(); ++i) {
      var var = factory.local("y" + i);
      var typeParam = factory.core(occurrences.get(i).computeType().computeTyped());
      lamParams.add(factory.param(true, Collections.singletonList(var), typeParam));
    }

    ConcreteExpression lam = factory.lam(lamParams, factory.meta("\\lam y_v => {!}", new MetaDefinition() {
      @Override
      public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        List<TypedExpression> checkedVars = new ArrayList<>();

        for (var param : lamParams) {
          var checkedVar =  typechecker.typecheck(factory.ref(param.getRefList().get(0)), null);
          assert checkedVar != null;
          checkedVars.add(checkedVar);
        }

        Map<Wrapper<CoreExpression>, Integer> indexOfSubExpr = new HashMap<>();

        for (int i = 0; i < occurrences.size(); ++i) {
          indexOfSubExpr.put(new Wrapper<>(occurrences.get(i)), i);
        }

        UncheckedExpression typeWithOccur = replaceSubexpr(normType, checkedVars, indexOfSubExpr, processor.getExprsToNormalize(), occurrences);

        /*final boolean[] subexprNormalized = {true};

        while (subexprNormalized[0]) {
          subexprNormalized[0] = false;
          typeWithOccur = typeWithOccur.replaceSubexpressions(expression -> {
            var newSubexpr = expression;
            if (processor.getExprsToNormalize().containsKey(expression)) {
              subexprNormalized[0] = true;
              newSubexpr = processor.getExprsToNormalize().get(expression);
            }
            Integer occurInd = indexOfSubExpr.get(new Wrapper<>(newSubexpr));
            if (occurInd != null) {
              return newSubexpr;
            }
            return newSubexpr == expression ? null : newSubexpr;
          }, true);
          if (typeWithOccur == null) break;
        }

        typeWithOccur = typeWithOccur == null ? null : typeWithOccur.replaceSubexpressions(expression -> {
          Integer occurInd = indexOfSubExpr.get(new Wrapper<>(expression));
          if (occurInd == null) return null;
          return checkedVars.get(occurInd).getExpression();
        }, false); /**/

        TypedExpression result = typeWithOccur != null ? Utils.tryTypecheck(typechecker, tc -> tc.check(typeWithOccur, refExpr)) : null;
        if (result == null) {
          errorReporter.report(typeWithOccur == null ? new SimplifyError(typechecker.getExpressionPrettifier(), occurrences, normType, refExpr) : new TypeError(typechecker.getExpressionPrettifier(), "Cannot substitute a variable. The resulting type is invalid", typeWithOccur, refExpr));
        }/**/
        return result;
        // return typeWithOccur;
      }
    }));

    var checkedLam = typechecker.typecheck(lam, null);

    if (checkedLam == null || checkedLam instanceof CoreErrorExpression) {
      return null;
    }
    var proofs = processor.simplificationOccurrences.stream().map(x -> isForward ? x.proj2 : x.proj2.inverse(factory, ext)).collect(Collectors.toList());
    return RewriteMeta.chainOfTransports(factory.ref(ext.transport.getRef(), refExpr.getPLevels(), refExpr.getHLevels()),
            checkedLam.getExpression(), proofs, expression, factory, ext);
  }

  @Override
  public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    var refExpr = contextData.getReferenceExpression();
    boolean isForward = contextData.getExpectedType() == null;
    CoreExpression expectedType = contextData.getExpectedType();
    List<? extends ConcreteArgument> args = contextData.getArguments();

    if (isForward && args.isEmpty()) {
      return null;
    }

    this.factory = ext.factory.withData(refExpr.getData());
    var expression = args.isEmpty() ? factory.ref(ext.prelude.getIdp().getRef()) : args.get(0).getExpression();
    CoreExpression type;

    if (isForward) {
      var checkedExpr = typechecker.typecheck(expression, null);
      type = checkedExpr == null ? null : checkedExpr.getType();
    } else {
      type = expectedType == null ? null : expectedType.getUnderlyingExpression();
    }

    if (type == null) {
      return Utils.typecheckWithAdditionalArguments(expression, typechecker, ext, 0, false);
    }

    this.typechecker = typechecker;
    this.refExpr = refExpr;
    this.errorReporter = typechecker.getErrorReporter();

    var transportedExpr = simplifyTypeOfExpression(expression, type, isForward);
    return transportedExpr == null ? null : typechecker.typecheck(transportedExpr, expectedType);
  }
}
