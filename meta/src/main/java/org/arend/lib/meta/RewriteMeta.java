package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteAppBuilder;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;

import org.arend.lib.error.TypeError;
import org.arend.lib.meta.equation.EqualitySolver;
import org.arend.lib.meta.equation.EquationSolver;
import org.arend.lib.meta.util.SubstitutionMeta;
import org.arend.lib.util.Utils;
import org.arend.lib.error.SubexprError;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;

public class RewriteMeta extends BaseMetaDefinition {
  private final StdExtension ext;
  private final boolean isForward;
  private final boolean isInverse;
  private final boolean useEqSolver;

  private EqualitySolver solver;

  public RewriteMeta(StdExtension ext, boolean isForward, boolean isInverse, boolean useEqSolver) {
    this.ext = ext;
    this.isForward = isForward;
    this.isInverse = isInverse;
    this.useEqSolver = useEqSolver;
  }

  @Override
  public boolean withoutLevels() {
    return false;
  }

  @Override
  public boolean[] argumentExplicitness() {
    return new boolean[] { false, true, true };
  }

  private void getNumber(ConcreteExpression expression, List<Integer> result, ErrorReporter errorReporter) {
    int n = Utils.getNumber(expression, errorReporter);
    if (n >= 1) {
      result.add(n - 1);
    }
  }

  @Override
  public @Nullable ConcreteExpression getConcreteRepresentation(@NotNull List<? extends ConcreteArgument> arguments) {
    return ext.factory.appBuilder(ext.factory.ref(ext.transportInv.getRef())).app(ext.factory.hole()).app(arguments.subList(arguments.get(0).isExplicit() ? 0 : 1, arguments.size())).build();
  }

  private EquationSolver.SubexprOccurrences matchSubexpr(CoreExpression subExpr, CoreExpression expr, ExpressionTypechecker tc, ConcreteReferenceExpression refExpr, List<Integer> occurrences, ConcreteFactory factory) {
    return solver.matchSubexpr(subExpr.computeTyped(), expr.computeTyped(), tc.getErrorReporter(), occurrences);
  }

  private class RewriteExpressionProcessor implements Function<CoreExpression, CoreExpression.FindAction> {
    private final CoreExpression subExpr;
    private final ExpressionTypechecker typechecker;
    private final ConcreteReferenceExpression refExpr;
    private final CoreExpression subExprType;
    private final ConcreteFactory factory;

    private List<Integer> occurrences;
    private final List<Pair<EquationSolver.SubexprOccurrences, CoreExpression>> foundOccurrences = new ArrayList<>();
    private final List<Integer> exactMatches = new ArrayList<>();

    public List<Integer> getExactMatches() {
      return exactMatches;
    }

    public List<Pair<EquationSolver.SubexprOccurrences, CoreExpression>> getFoundOccurrences() {
      return foundOccurrences;
    }

    public boolean allOccurrencesFound() { return occurrences == null || occurrences.isEmpty(); }

    public RewriteExpressionProcessor(CoreExpression subExpr, CoreExpression subExprType, List<Integer> occurrences, ExpressionTypechecker typechecker, ConcreteReferenceExpression refExpr) {
      this.subExpr = subExpr;
      this.occurrences = occurrences != null ? new ArrayList<>(occurrences) : null;
      this.typechecker = typechecker;
      this.refExpr = refExpr;
      this.subExprType = subExpr.computeType();
      this.factory = ext.factory.withData(refExpr.getData());
    }

    @Override
    public @Nullable CoreExpression.FindAction apply(@NotNull CoreExpression expression) {
      if (occurrences != null && occurrences.isEmpty()) return CoreExpression.FindAction.STOP;
      boolean ok;
      boolean exactMatch = false;
      boolean skip = false;
      EquationSolver.SubexprOccurrences subExprOccur = null;
      if (subExpr instanceof CoreFunCallExpression && expression instanceof CoreFunCallExpression && ((CoreFunCallExpression) subExpr).getDefinition() == ((CoreFunCallExpression) expression).getDefinition()) {
        ok = true;
        List<? extends CoreExpression> args1 = ((CoreFunCallExpression) subExpr).getDefCallArguments();
        if (args1.isEmpty()) {
          return CoreExpression.FindAction.CONTINUE;
        }
        List<? extends CoreExpression> args2 = ((CoreFunCallExpression) expression).getDefCallArguments();
        for (int i = 0; i < args1.size(); i++) {
          if (!typechecker.compare(args1.get(i), args2.get(i), CMP.EQ, refExpr, false, true, true)) {
            ok = false;
            break;
          }
        }
        exactMatch = true;
      } else {
        if (useEqSolver) {
          var subExprTypeFixed = subExprType;
          var expressionTypeFixed = expression.computeType();
          while (subExprTypeFixed instanceof CoreAppExpression) {
            subExprTypeFixed = ((CoreAppExpression) subExprTypeFixed).getFunction();
          }
          while (expressionTypeFixed instanceof CoreAppExpression) {
            expressionTypeFixed = ((CoreAppExpression) expressionTypeFixed).getFunction();
          }
          if (subExprTypeFixed instanceof CoreDefCallExpression && ((CoreDefCallExpression) subExprTypeFixed).getDefinition() == ext.equationMeta.catHom) {
            if (!(expressionTypeFixed instanceof CoreDefCallExpression)) {
              ok = false;
            } else {
              ok = ((CoreDefCallExpression) subExprTypeFixed).getDefinition() == ((CoreDefCallExpression) expressionTypeFixed).getDefinition();
            }
          } else {
            ok = typechecker.compare(subExprType, expression.computeType(), CMP.LE, refExpr, false, true, false);
          } /**/
        } else {
          ok = typechecker.compare(subExprType, expression.computeType(), CMP.LE, refExpr, false, true, false);
        }
        if (ok) {
          ok = typechecker.compare(subExpr, expression, CMP.EQ, refExpr, false, true, true);
          if (!ok) {
            if (useEqSolver) {
              subExprOccur = matchSubexpr(subExpr, expression, typechecker, refExpr, occurrences, factory);
              ok = subExprOccur.doesExist();
              //if (!ok) {
              if (occurrences != null) {
                if (ok) {
                  occurrences = new ArrayList<>(occurrences.subList(0, subExprOccur.numOccurrences));
                }
                if (!occurrences.isEmpty()) {
                  occurrences.set(0, occurrences.get(0) - subExprOccur.numOccurrencesSkipped);
                }
              }
              //}

              skip = !subExprOccur.subExprMissed;
            }
          } else {
            exactMatch = true;
          }
        }
      }
      if (exactMatch && occurrences != null) {
        if (occurrences.get(0) == 0) {
          occurrences.remove(0);
        } else {
          ok = false;
          occurrences.set(0, occurrences.get(0) - 1);
        }
      }
      if (ok) {
        typechecker.updateSavedState();
        if (exactMatch) {
          subExprOccur = EquationSolver.SubexprOccurrences.simpleSingletonOccur(factory, subExprType,factory.ref(ext.prelude.getIdp().getRef()));
          exactMatches.add(foundOccurrences.size());
        }
        foundOccurrences.add(new Pair<>(subExprOccur, expression));
        return CoreExpression.FindAction.SKIP;
      }
      typechecker.loadSavedState();
      return skip ? CoreExpression.FindAction.SKIP : CoreExpression.FindAction.CONTINUE;
    }
  }

  public static class EqProofConcrete {
    public ConcreteExpression proof;
    public ConcreteExpression left;
    public ConcreteExpression right;

    public EqProofConcrete(ConcreteExpression proof, ConcreteExpression left, ConcreteExpression right) {
      this.proof = proof;
      this.left = left;
      this.right = right;
    }

    public EqProofConcrete inverse(ConcreteFactory factory, StdExtension ext) {
      return new EqProofConcrete(factory.appBuilder(factory.ref(ext.inv.getRef()))/*.app(factory.hole(), false).app(left, false).app(right, false)*/.app(proof).build(), right, left);
    }
  }

  public static ConcreteExpression chainOfTransports(ConcreteExpression transport, CoreExpression type, List<EqProofConcrete> eqProofs, ConcreteExpression term, ConcreteFactory factory, StdExtension ext) {
    var result = term;
    var curType = type; //typechecker.typecheck(type, null);
    List<CoreBinding> paramList = new ArrayList<>();
    boolean isInverse = ((ConcreteReferenceExpression)transport).getReferent() == ext.transportInv.getRef();

    for (int i = 0; i < eqProofs.size(); ++i) {
      if (!(curType instanceof CoreLamExpression)) return null;
      var body = ((CoreLamExpression)(curType)).getBody();
      var param = ((CoreLamExpression)(curType)).getParameters();
      int finalI = i;
      paramList.add(param.getBinding());
      var absNewBody = SubstitutionMeta.makeLambda(body, paramList, factory, expression -> {
        var newBody = factory.core(expression.computeTyped());
        for (int j = finalI + 1; j < eqProofs.size(); ++j) {
          var left = !isInverse ? eqProofs.get(j).left : eqProofs.get(j).right;
          newBody = factory.appBuilder(newBody).app(left).build();
        }
        return newBody;
      });  //factory.lam(paramList, newBody);
      for (int j = 0; j < i; ++j) {
        var right = !isInverse ? eqProofs.get(j).right : eqProofs.get(j).left;
        absNewBody = factory.appBuilder(absNewBody).app(right).build();
      }
      var left = eqProofs.get(i).left; //isInverse ? eqProofs.get(i).left : eqProofs.get(i).right;//eqProofs.get(i).left; //
      var right = eqProofs.get(i).right; //isInverse ? eqProofs.get(i).right : eqProofs.get(i).left;//eqProofs.get(i).right; //
      result = factory.appBuilder(transport)//.app(factory.hole(), false)
              //.app(factory.core(transportType))
              .app(absNewBody) //.app(left, false).app(right, false)
              .app(eqProofs.get(i).proof)
              .app(result)
              .build();
      curType = body;
    }

    return result;
  }

  @Override
  public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    int currentArg = 0;
    ConcreteExpression occurrencesArg = args.get(0).isExplicit() ? null : args.get(currentArg++).getExpression();
    List<? extends ConcreteExpression> args0 = new ArrayList<>(Utils.getArgumentList(args.get(currentArg++).getExpression()));
    if (args0.isEmpty()) {
      return typechecker.typecheck(args.get(currentArg).getExpression(), contextData.getExpectedType());
    }

    CoreExpression expectedType = contextData.getExpectedType() == null ? null : contextData.getExpectedType().getUnderlyingExpression();
    boolean reverse = expectedType == null || args.size() > currentArg + 2;
    boolean isForward = reverse || this.isForward;

    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    if (args0.size() > 1) {
      if (isForward) {
        Collections.reverse(args0);
      }
      ConcreteExpression result = args.get(currentArg++).getExpression();
      for (int i = args0.size() - 1; i >= 0; i--) {
        ConcreteAppBuilder builder = factory.appBuilder(refExpr);
        if (occurrencesArg != null) builder.app(occurrencesArg, false);
        result = builder.app(args0.get(i)).app(result).build();
      }
      return typechecker.typecheck(factory.app(result, args.subList(currentArg, args.size())), contextData.getExpectedType());
    }
    ConcreteExpression arg0 = args0.get(0);

    // Collect occurrences
    List<Integer> occurrences;
    if (occurrencesArg != null) {
      occurrences = new ArrayList<>();
      for (ConcreteExpression expr : Utils.getArgumentList(occurrencesArg)) {
        getNumber(expr, occurrences, errorReporter);
      }
    } else {
      occurrences = null;
    }

    //noinspection SimplifiableConditionalExpression
    boolean isInverse = reverse && !this.isForward ? !this.isInverse : this.isInverse;

    // Add inference holes to functions and type-check the path argument
    TypedExpression path = Utils.typecheckWithAdditionalArguments(arg0, typechecker, ext, 0, false);
    if (path == null) {
      return null;
    }

    // Check that the first argument is a path
    CoreFunCallExpression eq = Utils.toEquality(path.getType(), errorReporter, arg0);
    if (eq == null) {
      return null;
    }

    ConcreteExpression transport = factory.ref((isInverse ? ext.transportInv : ext.transport).getRef(), refExpr.getPLevels(), refExpr.getHLevels());
    CoreExpression value = eq.getDefCallArguments().get(isInverse == isForward ? 2 : 1);

    // This case won't happen often, but sill possible
    if (!isForward && expectedType instanceof CoreInferenceReferenceExpression) {
      CoreExpression var = value.getUnderlyingExpression();
      if (var instanceof CoreInferenceReferenceExpression && ((CoreInferenceReferenceExpression) var).getVariable() == ((CoreInferenceReferenceExpression) expectedType).getVariable()) {
        if (!(occurrences == null || occurrences.isEmpty() || occurrences.size() == 1 && occurrences.contains(1))) {
          occurrences.remove(1);
          errorReporter.report(new SubexprError(typechecker.getExpressionPrettifier(), occurrences, var, null, expectedType, refExpr));
          return null;
        }
        ArendRef ref = factory.local("T");
        return typechecker.typecheck(factory.app(transport, true, Arrays.asList(
          factory.lam(Collections.singletonList(factory.param(ref)), factory.ref(ref)),
          factory.core("transport (\\lam T => T) {!} _", path),
          args.get(currentArg).getExpression())), null);
      }
      isForward = true;
    }

    TypedExpression lastArg;
    CoreExpression type;
    if (isForward) {
      lastArg = typechecker.typecheck(args.get(currentArg++).getExpression(), null);
      if (lastArg == null) {
        return null;
      }
      type = lastArg.getType();
    } else {
      lastArg = null;
      type = expectedType;
    }

    if (useEqSolver) {
      solver = new EqualitySolver(ext.equationMeta, typechecker, factory, refExpr);
      solver.setValuesType(value.computeType());
      solver.setUseHypotheses(false);
      solver.initializeSolver();
    }

    ConcreteExpression concretePath = factory.core(path);
    CoreExpression normType = type.normalize(NormalizationMode.RNF);
    ConcreteExpression term = lastArg == null ? args.get(currentArg++).getExpression() : factory.core("transport _ _ {!}", lastArg);
    var occurVars = new ArrayList<ArendRef>();
    var eqProofs = new ArrayList<EqProofConcrete>();

    var processor = new RewriteExpressionProcessor(value, eq.getDefCallArguments().get(0), occurrences, typechecker, refExpr);
    typechecker.withCurrentState(tc -> normType.processSubexpression(processor));

    var foundOccurs = processor.getFoundOccurrences();
    int firstExactMatch = processor.getExactMatches().isEmpty() ? -1 : processor.getExactMatches().get(0);

    if (foundOccurs.isEmpty() || !processor.allOccurrencesFound()) {
      errorReporter.report(new SubexprError(typechecker.getExpressionPrettifier(), occurrences, value, null, normType, refExpr));
      return null;
    }

    Map<Integer, Integer> occurIndToVarInd = new HashMap<>();

    for (int i = 0; i < foundOccurs.size(); ++i) {
      boolean isExactMatch = processor.getExactMatches().contains(i);
      if (i <= firstExactMatch || !isExactMatch) {
        var var = factory.local("y" + i);
        occurIndToVarInd.put(i, occurVars.size());
        occurVars.add(var);
        var left = factory.core(isInverse == isForward ? eq.getDefCallArguments().get(1).computeTyped() : foundOccurs.get(i).proj2.computeTyped());
        var right = factory.core(isInverse == isForward ? foundOccurs.get(i).proj2.computeTyped() : eq.getDefCallArguments().get(2).computeTyped());
        if (isExactMatch) {
          eqProofs.add(new EqProofConcrete(concretePath, left, right));
        } else {
          var subExprOccur = foundOccurs.get(i).proj1;
          var fixedLeft = factory.appBuilder(subExprOccur.exprWithOccurrences).app(left).build();
          var fixedRight = factory.appBuilder(subExprOccur.exprWithOccurrences).app(right).build();
          var occurPathTransport = factory.appBuilder(factory.ref(ext.pmap.getRef())).app(subExprOccur.exprWithOccurrences).app(concretePath).build();
          var eqProof = factory.appBuilder(factory.ref(ext.concat.getRef())).app(subExprOccur.equalityProof).app(occurPathTransport).build();
          eqProofs.add(new EqProofConcrete(eqProof, fixedLeft, fixedRight)); // (factory.core(solver.finalize(eqProof)));
        }
      } else {
        occurIndToVarInd.put(i, occurVars.size() - 1);
      }
    }

    var lamParams = new ArrayList<ConcreteParameter>();

    for (int i = 0; i < occurVars.size(); ++i) {
      var var = occurVars.get(i);
      var typeParam = useEqSolver ? factory.core(foundOccurs.get(i).proj2.computeType().computeTyped()) : factory.core(eq.getDefCallArguments().get(0).computeTyped());
      lamParams.add(factory.param(true, Collections.singletonList(var), typeParam));
    }

    ConcreteExpression lam = factory.lam(lamParams, factory.meta("\\lam y_v => {!}", new MetaDefinition() {
      @Override
      public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        List<TypedExpression> checkedVars = new ArrayList<>();

        for (var var : occurVars) {
          var checkedVar =  typechecker.typecheck(factory.ref(var), null);
          assert checkedVar != null;
          checkedVars.add(checkedVar);
        }

        Map<CoreExpression, Integer> indexOfSubExpr = new HashMap<>();

        for (int i = 0; i < foundOccurs.size(); ++i) {
          indexOfSubExpr.put(foundOccurs.get(i).proj2, i);
        }

        // TypedExpression exactMatchVar = finalExactMatchParam != null ? typechecker.typecheck(factory.ref(finalExactMatchParam.getBinding()), null) : var;
        var typeWithOccur = normType.replaceSubexpressions(expression -> {
          Integer occurInd = indexOfSubExpr.get(expression);
          if (occurInd == null) return null;
          Integer varInd = occurIndToVarInd.get(occurInd);
          if (varInd == null) return null;
          return checkedVars.get(varInd).getExpression();
        }, false);

        TypedExpression result = typeWithOccur != null ? Utils.tryTypecheck(typechecker, tc -> tc.check(typeWithOccur, refExpr)) : null;
        if (result == null) {
          errorReporter.report(typeWithOccur == null ? new SubexprError(typechecker.getExpressionPrettifier(), occurrences, value, null, normType, refExpr) : new TypeError(typechecker.getExpressionPrettifier(), "Cannot substitute a variable. The resulting type is invalid", typeWithOccur, refExpr));
        }
        return result;
      }
    }));

    var checkedLam = typechecker.typecheck(lam, null);

    if (checkedLam == null || checkedLam instanceof CoreErrorExpression) {
      return null;
    }

    term = chainOfTransports(transport, checkedLam.getExpression(), eqProofs, term, factory, ext);

    if (term == null) return null;

    term = factory.appBuilder(term)
            .app(args.subList(currentArg, args.size()))
            .build();

    if (useEqSolver) return solver.finalize(term);
    return typechecker.typecheck(term, expectedType);
  }
}
