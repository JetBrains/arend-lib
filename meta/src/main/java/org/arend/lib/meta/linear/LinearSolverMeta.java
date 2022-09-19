package org.arend.lib.meta.linear;

import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class LinearSolverMeta extends BaseMetaDefinition {
  private final StdExtension ext;

  @Dependency(module = "Algebra.Linear.Solver", name = "Data.solveContrHProblem") CoreFunctionDefinition solveContrHProblem;
  @Dependency(module = "Algebra.Linear.Solver", name = "Data.solve<=HProblem")    CoreFunctionDefinition solveLeqHProblem;
  @Dependency(module = "Algebra.Linear.Solver", name = "Data.solve<HProblem")     CoreFunctionDefinition solveLessHProblem;
  @Dependency(module = "Algebra.Linear.Solver", name = "Data.solve=HProblem")     CoreFunctionDefinition solveEqHProblem;
  @Dependency(module = "Algebra.Linear.Solver", name = "Operation.Less")          CoreConstructor less;
  @Dependency(module = "Algebra.Linear.Solver", name = "Operation.LessOrEquals")  CoreConstructor lessOrEquals;
  @Dependency(module = "Algebra.Linear.Solver", name = "Operation.Equals")        CoreConstructor equals;
  @Dependency(module = "Algebra.Linear.Solver")                                   CoreClassDefinition SemiringData;

  public LinearSolverMeta(StdExtension ext) {
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

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    return new LinearSolver(typechecker, contextData.getMarker(), ext).solve(contextData.getExpectedType(), contextData.getArguments().isEmpty() ? null : contextData.getArguments().get(0).getExpression());
  }
}
