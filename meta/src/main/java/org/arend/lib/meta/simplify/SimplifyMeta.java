package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreErrorExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFieldCallExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.error.SimplifyError;
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
  public boolean requireExpectedType() {
    return true;
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }

  private class SimplifyExpressionProcessor implements Function<CoreExpression, CoreExpression.FindAction> {

    private final List<Pair<CoreExpression, RewriteMeta.EqProofConcrete>> simplificationOccurrences = new ArrayList<>();

    public List<Pair<CoreExpression, RewriteMeta.EqProofConcrete>> getSimplificationOccurrences() {
      return simplificationOccurrences;
    }

    public SimplifyExpressionProcessor() {

    }

    @Override
    public CoreExpression.FindAction apply(CoreExpression expression) {
      var simplificationRules = getSimplificationRulesForType(expression.computeType());
      var simplifiedExpr = expression.computeTyped();
      ConcreteExpression right = null;
      ConcreteExpression path = null;
      boolean skip = false;
      boolean keepSimplifying = true;
      while (keepSimplifying) {
        keepSimplifying = false;
        for (var rule : simplificationRules) {
          var simplificationRes = rule.apply(simplifiedExpr);
          skip = true;
          if (simplificationRes == null) continue;
          keepSimplifying = true;
          right = simplificationRes.right;
          if (path == null) {
            path = simplificationRes.proof;
          } else {
            path = factory.appBuilder(factory.ref(ext.concat.getRef())).app(path).app(simplificationRes.proof).build();
          }
          simplifiedExpr = typechecker.typecheck(simplificationRes.right, simplifiedExpr.getType());
          if (simplifiedExpr == null) return CoreExpression.FindAction.SKIP;
        }
      }
      if (path == null) {
        if (skip) {
          return CoreExpression.FindAction.SKIP;
        }
        return CoreExpression.FindAction.CONTINUE;
      }
      simplificationOccurrences.add(new Pair<>(expression, new RewriteMeta.EqProofConcrete(path, factory.core(expression.computeTyped()), right)));
      return CoreExpression.FindAction.SKIP;
    }
  }

  private List<SimplificationRule> getSimplificationRulesForType(CoreExpression type) {
    var rules = new ArrayList<SimplificationRule>();
    type = type == null ? null : type.normalize(NormalizationMode.WHNF);
    if (type instanceof CoreFieldCallExpression) {
      if (((CoreFieldCallExpression) type).getDefinition() == ext.carrier) {
        TypedExpression instance = ((CoreFieldCallExpression) type).getArgument().computeTyped();
        CoreClassCallExpression classCall = instance.getType() instanceof CoreClassCallExpression ? (CoreClassCallExpression) instance.getType() : null;
        if (classCall != null) {
          if (classCall.getDefinition().isSubClassOf(ext.equationMeta.Monoid)) {
            rules.add(new MonoidIdentityRule(instance, classCall, ext, refExpr, typechecker, false));
          } else if (classCall.getDefinition().isSubClassOf(ext.equationMeta.AddMonoid)) {
            rules.add(new MonoidIdentityRule(instance, classCall, ext, refExpr, typechecker, true));
          }
          if (classCall.getDefinition().isSubClassOf(ext.equationMeta.Semiring)) {
            rules.add(new MultiplicationByZeroRule(instance, classCall, ext, refExpr, typechecker));
          }
          if (classCall.getDefinition().isSubClassOf(ext.equationMeta.Ring)) {
            rules.add(new MulOfNegativesRule(instance, classCall, ext, refExpr, typechecker));
          }
          if (classCall.getDefinition().isSubClassOf(ext.equationMeta.AddGroup)) {
            rules.add(new DoubleNegationRule(instance, classCall, ext, refExpr, typechecker));
          }
        }
      }
    }
    return rules;
  }

  private ConcreteExpression simplifyTypeOfExpression(ConcreteExpression expression, CoreExpression type) {
    var processor = new SimplifyExpressionProcessor();
    typechecker.withCurrentState(tc -> type.processSubexpression(processor));

    var occurrences = processor.getSimplificationOccurrences().stream().map(x -> x.proj1).collect(Collectors.toList());
    var lamParams = new ArrayList<ConcreteParameter>();

    if (occurrences.isEmpty()) return expression; //factory.core(expression.computeTyped());

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

        Map<CoreExpression, Integer> indexOfSubExpr = new HashMap<>();

        for (int i = 0; i < occurrences.size(); ++i) {
          indexOfSubExpr.put(occurrences.get(i), i);
        }

        var typeWithOccur = type.replaceSubexpressions(expression -> {
          Integer occurInd = indexOfSubExpr.get(expression);
          if (occurInd == null) return null;
          return checkedVars.get(occurInd).getExpression();
        }, false);

        TypedExpression result = typeWithOccur != null ? Utils.tryTypecheck(typechecker, tc -> tc.check(typeWithOccur, refExpr)) : null;
        if (result == null) {
          errorReporter.report(new SimplifyError(occurrences, type, refExpr));
        }
        return result;
      }
    }));

    var checkedLam = typechecker.typecheck(lam, null);

    if (checkedLam == null || checkedLam instanceof CoreErrorExpression) {
      return null;
    }
    var proofs = processor.simplificationOccurrences.stream().map(x -> x.proj2.inverse(factory, ext)).collect(Collectors.toList());
    return RewriteMeta.chainOfTransports(factory.ref(ext.transport.getRef(), refExpr.getPLevels(), refExpr.getHLevels()),
            checkedLam.getExpression(), proofs, expression, factory, ext);
  }

  @Override
  public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    var refExpr = contextData.getReferenceExpression();
    var expectedType = contextData.getExpectedType() == null ? null : contextData.getExpectedType().getUnderlyingExpression();
    List<? extends ConcreteArgument> args = contextData.getArguments();

    this.factory = ext.factory.withData(refExpr.getData());
    var expression = args.isEmpty() ? factory.ref(ext.prelude.getIdp().getRef()) : args.get(0).getExpression();

    if (expectedType == null) {
      return Utils.typecheckWithAdditionalArguments(expression, typechecker, ext, 0, false);
    }

    this.typechecker = typechecker;
    this.refExpr = refExpr;
    this.errorReporter = typechecker.getErrorReporter();

    var transportedExpr = simplifyTypeOfExpression(expression, expectedType);
    return transportedExpr == null ? null : typechecker.typecheck(transportedExpr, expectedType);
  }
}
