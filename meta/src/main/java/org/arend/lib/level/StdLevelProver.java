package org.arend.lib.level;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcretePattern;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class StdLevelProver implements LevelProver {
  private final StdExtension ext;

  public StdLevelProver(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable TypedExpression prove(@NotNull CoreExpression expression, @NotNull CoreExpression type, int level, @NotNull ConcreteSourceNode marker, @NotNull ExpressionTypechecker typechecker) {
    if (level != -1) {
      return null;
    }

    return Utils.tryTypecheck(typechecker, tc -> {
      ConcreteFactory factory = ext.factory.withData(marker.getData());
      ArendRef x = factory.local("x");
      ArendRef y = factory.local("y");
      ConcreteExpression result = proveProp(expression, factory.ref(x), factory.ref(y), marker, factory, typechecker);
      return result == null ? null : typechecker.typecheck(factory.lam(Arrays.asList(factory.param(x), factory.param(y)), result), type);
    });
  }

  private ConcreteExpression proveProp(CoreExpression expression, ConcreteReferenceExpression leftExpr, ConcreteReferenceExpression rightExpr, ConcreteSourceNode marker, ConcreteFactory factory, ExpressionTypechecker typechecker) {
    CoreExpression type = expression.normalize(NormalizationMode.WHNF);
    CoreExpression typeType = type.computeType().normalize(NormalizationMode.WHNF);
    if (typeType instanceof CoreUniverseExpression && ((CoreUniverseExpression) typeType).getSort().isProp()) {
      return factory.app(factory.ref(ext.prelude.getInProp().getRef()), true, Arrays.asList(leftExpr, rightExpr));
    }

    if (type instanceof CoreDataCallExpression) {
      ConcreteExpression result = provePropDataType((CoreDataCallExpression) type, leftExpr, rightExpr, marker, factory);
      if (result != null) {
        return result;
      }
    }

    for (CoreBinding binding : typechecker.getFreeBindingsList()) {
      List<CoreParameter> parameters = new ArrayList<>();
      CoreExpression codomain = binding.getTypeExpr().getPiParameters(parameters);
      if (parameters.size() != 2) {
        continue;
      }

      CoreFunCallExpression equality = codomain.toEquality();
      if (equality != null) {
        List<? extends CoreExpression> args = equality.getDefCallArguments();
        if (args.get(1) instanceof CoreReferenceExpression && args.get(2) instanceof CoreReferenceExpression && ((CoreReferenceExpression) args.get(1)).getBinding() == parameters.get(0).getBinding() && ((CoreReferenceExpression) args.get(2)).getBinding() == parameters.get(1).getBinding() && typechecker.compare(args.get(0), type, CMP.EQ, marker, false, true)) {
          return factory.app(factory.ref(binding), true, Arrays.asList(leftExpr, rightExpr));
        }
      }
    }

    // TODO: Sigma types, pi types, equality (i.e., rising level), heterogeneous path types, recursive data types, dependently typed constructors

    return ext.contradictionMeta.check(null, null, true, marker, typechecker);
  }

  private ConcreteExpression provePropDataType(CoreDataCallExpression dataCall, ConcreteReferenceExpression leftExpr, ConcreteReferenceExpression rightExpr, ConcreteSourceNode marker, ConcreteFactory factory) {
    if (!dataCall.getDefinition().getRecursiveDefinitions().isEmpty()) {
      return null;
    }
    List<CoreConstructor> constructors = dataCall.computeMatchedConstructors();
    if (constructors == null) {
      return null;
    }
    for (CoreConstructor constructor : constructors) {
      if (!constructor.getParameters().hasNext() || !constructor.getParameters().getNext().hasNext()) {
        continue;
      }

      Set<CoreBinding> bindings = new HashSet<>();
      for (CoreParameter parameter = constructor.getParameters(); parameter.hasNext(); parameter = parameter.getNext()) {
        if (parameter.getTypeExpr().findFreeBindings(bindings) != null) {
          return null;
        }
        bindings.add(parameter.getBinding());
      }
    }

    List<ConcreteClause> clauses = new ArrayList<>();
    for (CoreConstructor con1 : constructors) {
      for (CoreConstructor con2 : constructors) {
        List<ConcretePattern> subPatterns1 = new ArrayList<>();
        List<ConcretePattern> subPatterns2 = new ArrayList<>();
        List<ArendRef> refs1 = con1 == con2 ? new ArrayList<>() : null;
        List<ArendRef> refs2 = con1 == con2 ? new ArrayList<>() : null;
        for (CoreParameter param = con1.getParameters(); param.hasNext(); param = param.getNext()) {
          ArendRef ref = factory.local(ext.renamerFactory.getNameFromType(param.getTypeExpr(), null) + "1");
          subPatterns1.add(factory.refPattern(ref, null));
          if (refs1 != null) {
            refs1.add(ref);
          }
        }
        for (CoreParameter param = con2.getParameters(); param.hasNext(); param = param.getNext()) {
          ArendRef ref = factory.local(ext.renamerFactory.getNameFromType(param.getTypeExpr(), null) + "2");
          subPatterns2.add(factory.refPattern(ref, null));
          if (refs2 != null) {
            refs2.add(ref);
          }
        }

        // We need a meta here because the context changes and we use it in both proveProp and ContradictionMeta.check
        clauses.add(factory.clause(Arrays.asList(factory.conPattern(con1.getRef(), subPatterns1), factory.conPattern(con2.getRef(), subPatterns2)), factory.meta("case " + con1.getName() + " " + con2.getName(), new MetaDefinition() {
          @Override
          public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
            ConcreteExpression result;
            if (con1 == con2) {
              CoreParameter conParam = dataCall.getConstructorParameters(con1);
              if (conParam.hasNext()) {
                ArendRef iRef = factory.local("i");
                ConcreteExpression iExpr = factory.ref(iRef);
                List<ConcreteArgument> args = new ArrayList<>();
                for (int i = 0; conParam.hasNext(); conParam = conParam.getNext(), i++) {
                  ConcreteExpression expr = proveProp(conParam.getTypeExpr(), factory.ref(refs1.get(i)), factory.ref(refs2.get(i)), marker, factory, typechecker);
                  if (expr == null) {
                    return null;
                  }
                  args.add(factory.arg(factory.app(factory.ref(ext.prelude.getAt().getRef()), true, Arrays.asList(expr, iExpr)), conParam.isExplicit()));
                }
                result = factory.app(factory.ref(ext.prelude.getPathCon().getRef()), true, Collections.singletonList(factory.lam(Collections.singletonList(factory.param(iRef)), factory.app(factory.ref(con1.getRef()), args))));
              } else {
                result = factory.ref(ext.prelude.getIdp().getRef());
              }
            } else {
              result = ext.contradictionMeta.check(null, null, true, marker, typechecker);
            }
            return result == null ? null : typechecker.typecheck(result, contextData.getExpectedType());
          }
        })));
      }
    }
    return factory.caseExpr(false, Arrays.asList(factory.caseArg(leftExpr, null), factory.caseArg(rightExpr, null)), factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(leftExpr, rightExpr)), null, clauses);
  }
}
