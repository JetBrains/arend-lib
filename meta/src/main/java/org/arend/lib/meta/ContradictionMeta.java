package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.expr.CoreDataCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CorePiExpression;
import org.arend.ext.core.expr.UncheckedExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.error.TypeError;
import org.arend.lib.util.ContextHelper;
import org.arend.lib.util.Pair;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class ContradictionMeta extends BaseMetaDefinition {
  public final StdExtension ext;

  public ContradictionMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { false };
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ContextHelper contextHelper = new ContextHelper(contextData.getArguments().isEmpty() ? null : contextData.getArguments().get(0).getExpression());
    ConcreteFactory factory = ext.factory.withData(contextData.getReferenceExpression().getData());

    CoreExpression type = null;
    ConcreteExpression contr = null;
    List<Pair<Object, CorePiExpression>> piExpressions = new ArrayList<>();
    boolean searchForContradiction = true;
    if (!contextData.getArguments().isEmpty() && contextHelper.meta == null) {
      TypedExpression contradiction = typechecker.typecheck(contextData.getArguments().get(0).getExpression(), null);
      if (contradiction == null) {
        return null;
      }
      type = contradiction.getType().normalize(NormalizationMode.WHNF);
      if (isEmpty(type)) {
        contr = factory.core(null, contradiction);
      } else if (type instanceof CorePiExpression) {
        piExpressions.add(new Pair<>(contradiction, (CorePiExpression) type));
        searchForContradiction = false;
      } else {
        typechecker.getErrorReporter().report(new TypeError("The expression does not prove a contradiction", type, contextData.getArguments().get(0).getExpression()));
        return null;
      }
    }

    if (contr == null) {
      Values values = new Values(typechecker, contextData.getReferenceExpression());
      Map<Integer, CoreBinding> assumptions = new HashMap<>();
      for (CoreBinding binding : contextHelper.getAllBindings(typechecker)) {
        type = binding.getTypeExpr().normalize(NormalizationMode.WHNF);
        if (isEmpty(type)) {
          contr = factory.ref(binding);
          break;
        }
        CoreBinding prev = assumptions.putIfAbsent(values.addValue(type), binding);
        if (searchForContradiction && type instanceof CorePiExpression && prev == null) {
          piExpressions.add(new Pair<>(binding, (CorePiExpression) type));
        }
      }

      if (contr == null) {
        loop:
        for (Pair<Object, CorePiExpression> pair : piExpressions) {
          List<CoreParameter> parameters = new ArrayList<>();
          type = pair.proj2.getPiParameters(parameters);
          if (!isEmpty(type)) {
            continue;
          }

          List<ConcreteArgument> arguments = new ArrayList<>();
          Map<CoreBinding, CoreExpression> subst = new HashMap<>();
          for (int i = 0; i < parameters.size(); i++) {
            CoreParameter parameter = parameters.get(i);
            boolean isFree = false;
            for (int j = i + 1; j < parameters.size(); j++) {
              if (parameters.get(j).getTypeExpr().findFreeBinding(parameter.getBinding())) {
                isFree = true;
                break;
              }
            }

            ConcreteExpression argExpr;
            UncheckedExpression paramType = parameter.getTypeExpr().findFreeBindings(subst.keySet()) != null ? parameter.getTypeExpr().substitute(subst) : parameter.getTypeExpr();
            if (isFree) {
              CoreExpression checkedType;
              if (paramType instanceof CoreExpression) {
                checkedType = (CoreExpression) paramType;
              } else {
                TypedExpression typedExpr = typechecker.check(paramType, contextData.getReferenceExpression());
                if (typedExpr == null) {
                  continue loop;
                }
                checkedType = typedExpr.getExpression();
              }
              argExpr = factory.hole();
              subst.put(parameter.getBinding(), Objects.requireNonNull(typechecker.typecheck(argExpr, checkedType)).getExpression());
            } else {
              int index = values.getValue(paramType.normalize(NormalizationMode.WHNF));
              if (index == -1) {
                continue loop;
              }
              argExpr = factory.ref(assumptions.get(index));
            }

            arguments.add(factory.arg(argExpr, parameter.isExplicit()));
          }
          contr = factory.app(pair.proj1 instanceof CoreBinding ? factory.ref((CoreBinding) pair.proj1) : factory.core(null, (TypedExpression) pair.proj1), arguments);
        }

        if (contr == null) {
          typechecker.getErrorReporter().report(new TypecheckingError("Cannot infer contradiction", contextData.getReferenceExpression()));
          return null;
        }
      }
    }

    return typechecker.typecheck(contextData.getExpectedType() != null && contextData.getExpectedType().compare(type, CMP.EQ) ? contr : factory.caseExpr(false, Collections.singletonList(factory.caseArg(contr, null, null)), contextData.getExpectedType() != null ? null : factory.ref(ext.Empty.getRef()), null), contextData.getExpectedType());
  }

  private static boolean isEmpty(CoreExpression type) {
    if (type instanceof CoreDataCallExpression) {
      List<CoreConstructor> constructors = ((CoreDataCallExpression) type).computeMatchedConstructors();
      return constructors != null && constructors.isEmpty();
    }
    return false;
  }
}
