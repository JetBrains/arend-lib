package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteAppExpression;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFunCallExpression;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.MetaRef;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class EquationMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  public EquationMeta(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ErrorReporter errorReporter = typechecker.getErrorReporter();
    ConcreteReferenceExpression refExpr = contextData.getReferenceExpression();

    // values will contain ConcreteExpression (which correspond to implicit arguments) and TypedExpression (which correspond to explicit arguments).
    List<Object> values = new ArrayList<>();

    CoreFunCallExpression equality;
    if (contextData.getExpectedType() != null) {
      equality = Utils.toEquality(contextData.getExpectedType(), errorReporter, refExpr);
      if (equality == null) {
        return null;
      }
    } else {
      equality = null;
    }
    CoreExpression type = equality == null ? null : equality.getDefCallArguments().get(0);

    for (ConcreteArgument argument : contextData.getArguments()) {
      if (argument.isExplicit()) {
        TypedExpression value = typechecker.typecheck(argument.getExpression(), type);
        if (value == null) {
          return null;
        }
        values.add(value);
      } else {
        values.add(argument.getExpression());
      }
    }

    if (equality != null) {
      if (values.isEmpty() || !(values.get(0) instanceof TypedExpression) || !typechecker.compare(equality.getDefCallArguments().get(1), ((TypedExpression) values.get(0)).getExpression(), CMP.EQ, refExpr, false, true)) {
        values.add(0, equality.getDefCallArguments().get(1).computeTyped());
      }
      if (values.isEmpty() || !(values.get(values.size() - 1) instanceof TypedExpression) || !typechecker.compare(equality.getDefCallArguments().get(2), ((TypedExpression) values.get(values.size() - 1)).getExpression(), CMP.EQ, refExpr, false, true)) {
        values.add(equality.getDefCallArguments().get(2).computeTyped());
      }
    }

    // If values.size() <= 1, then we don't have expected type
    if (values.isEmpty()) {
      errorReporter.report(new TypecheckingError("Cannot infer type of the expression", refExpr));
      return null;
    }

    // If values.size() == 1, we either return the implicit argument or idp {_} {a}, where a is the explicit argument
    ConcreteFactory factory = ext.factory.withData(refExpr.getData());
    if (values.size() == 1) {
      ConcreteExpression result = values.get(0) instanceof ConcreteExpression
        ? (ConcreteExpression) values.get(0)
        : factory.app(factory.ref(ext.prelude.getIdp().getRef()), false, Arrays.asList(factory.hole(), factory.core(null, (TypedExpression) values.get(0))));
      return typechecker.typecheck(result, null);
    }

    boolean hasMissingProofs = false;
    for (int i = 0; i < values.size() - 1; i++) {
      if (values.get(i) instanceof TypedExpression && values.get(i + 1) instanceof TypedExpression) {
        hasMissingProofs = true;
      } else if (isUsingOrHiding(getMeta(values.get(i)))) {
        if (i > 0 && values.get(i - 1) instanceof TypedExpression && values.get(i + 1) instanceof TypedExpression) {
          hasMissingProofs = true;
        } else {
          errorReporter.report(new TypecheckingError("Hints must be between explicit arguments", (ConcreteExpression) values.get(i)));
          values.remove(i--);
        }
      }
    }

    CoreClassDefinition classDef;
    AlgebraSolverMeta.State state;
    if (hasMissingProofs) {
      if (type == null) {
        for (Object value : values) {
          if (value instanceof TypedExpression) {
            type = ((TypedExpression) value).getType();
            break;
          }
        }
      }

      classDef = ext.algebraMeta.getClassDef(type);
      if (classDef == null) {
        errorReporter.report(new TypecheckingError("Cannot infer missing proofs", refExpr));
        return null;
      }
      state = new AlgebraSolverMeta.State(typechecker, refExpr, factory);
    } else {
      classDef = null;
      state = null;
    }

    AlgebraSolverMeta.CompiledTerm lastCompiled = null;
    List<ConcreteExpression> equalities = new ArrayList<>();
    for (int i = 0; i < values.size(); i++) {
      MetaDefinition meta = getMeta(values.get(i));
      if (isUsingOrHiding(meta) || values.get(i) instanceof TypedExpression && i + 1 < values.size() && values.get(i + 1) instanceof TypedExpression) {
        AlgebraSolverMeta.CompiledTerm left = lastCompiled != null ? lastCompiled : ext.algebraMeta.compileTerm(state, ((TypedExpression) values.get(isUsingOrHiding(meta) ? i - 1 : i)).getExpression());
        AlgebraSolverMeta.CompiledTerm right = ext.algebraMeta.compileTerm(state, ((TypedExpression) values.get(i + 1)).getExpression());
        lastCompiled = right;
        assert state != null;

        ConcreteExpression argument = isUsingOrHiding(meta) ? ((ConcreteAppExpression) values.get(i)).getArguments().get(0).getExpression() : null;
        ConcreteExpression result = meta instanceof UsingMeta
            ? ext.algebraMeta.solve(state, ((UsingMeta) meta).keepOldContext ? null : Collections.emptyList(), ((UsingMeta) meta).getNewBindings(argument, typechecker), classDef, left, right, null)
            : meta instanceof HidingMeta
              ? ext.algebraMeta.solve(state, HidingMeta.updateBindings(argument, typechecker), Collections.emptyList(), classDef, left, right, null)
              : ext.algebraMeta.solve(state, null, Collections.emptyList(), classDef, left, right, null);
        if (result == null) {
          return null;
        }
        equalities.add(result);
      } else if (values.get(i) instanceof ConcreteExpression) {
        TypedExpression left = i > 0 && values.get(i - 1) instanceof TypedExpression ? (TypedExpression) values.get(i - 1) : null;
        TypedExpression right = i < values.size() - 1 && values.get(i + 1) instanceof TypedExpression ? (TypedExpression) values.get(i + 1) : null;
        CoreExpression eqType;
        if (left != null && right != null) {
          TypedExpression result = typechecker.typecheck(factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(factory.core(null, left), factory.core(null, right))), null);
          if (result == null) {
            return null;
          }
          eqType = result.getExpression();
        } else {
          eqType = null;
        }

        TypedExpression result = typechecker.typecheck((ConcreteExpression) values.get(i), eqType);
        if (result == null) {
          return null;
        }
        equalities.add(factory.core(null, result));
        lastCompiled = null;
      }
    }

    ConcreteExpression result = equalities.get(equalities.size() - 1);
    for (int i = equalities.size() - 2; i >= 0; i--) {
      result = factory.app(factory.ref(ext.concat.getRef()), true, Arrays.asList(equalities.get(i), result));
    }
    return hasMissingProofs ? ext.algebraMeta.finalizeState(state, result) : typechecker.typecheck(result, null);
  }

  private static MetaDefinition getMeta(Object expression) {
    if (!(expression instanceof ConcreteAppExpression)) {
      return null;
    }
    ConcreteAppExpression appExpr = (ConcreteAppExpression) expression;
    if (appExpr.getArguments().size() != 1 || !(appExpr.getFunction() instanceof ConcreteReferenceExpression)) {
      return null;
    }
    ArendRef ref = ((ConcreteReferenceExpression) appExpr.getFunction()).getReferent();
    return ref instanceof MetaRef ? ((MetaRef) ref).getDefinition() : null;
  }

  private static boolean isUsingOrHiding(MetaDefinition meta) {
    return meta instanceof UsingMeta || meta instanceof HidingMeta;
  }
}
