package org.arend.lib.meta.linear;

import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
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

  @Dependency(module = "Algebra.Linear.Solver", name = "LinearData.solveContrProblem")  CoreFunctionDefinition solveContrProblem;
  @Dependency(module = "Algebra.Linear.Solver", name = "LinearData.solve<=Problem")     CoreFunctionDefinition solveLeqProblem;
  @Dependency(module = "Algebra.Linear.Solver", name = "LinearData.solve<Problem")      CoreFunctionDefinition solveLessProblem;
  @Dependency(module = "Algebra.Linear.Solver", name = "LinearData.solve=Problem")      CoreFunctionDefinition solveEqProblem;
  @Dependency(module = "Algebra.Linear.Solver", name = "Operation.Less")                CoreConstructor less;
  @Dependency(module = "Algebra.Linear.Solver", name = "Operation.LessOrEquals")        CoreConstructor lessOrEquals;
  @Dependency(module = "Algebra.Linear.Solver", name = "Operation.Equals")              CoreConstructor equals;
  @Dependency(module = "Algebra.Linear.Solver")                                         CoreClassDefinition LinearSemiringData;
  @Dependency(module = "Algebra.Linear.Solver")                                         CoreClassDefinition LinearRingData;
  @Dependency(module = "Algebra.Linear.Solver")                                         CoreClassDefinition LinearRatData;
  @Dependency(module = "Arith.Int", name = "pos<=pos")                                  CoreFunctionDefinition posLEpos;
  @Dependency(module = "Arith.Int", name = "pos<pos")                                   CoreFunctionDefinition posLpos;
  @Dependency(module = "Arith.Rat", name = "fromInt_<=")                                CoreFunctionDefinition fromIntLE;
  @Dependency(module = "Arith.Rat", name = "fromInt_<")                                 CoreFunctionDefinition fromIntL;
  @Dependency(module = "Order.PartialOrder", name = "Preorder.=_<=")                    CoreFunctionDefinition eqToLeq;

  @Dependency(module = "Algebra.Ordered")                                               public CoreClassDefinition OrderedAAlgebra;
  @Dependency(module = "Algebra.Module", name = "LModule.R")                            public CoreClassField moduleRing;
  @Dependency(module = "Algebra.Linear.Solver")                                         CoreClassDefinition LinearRatAlgebraData;

  @Dependency(module = "Algebra.Algebra", name = "AAlgebra.coefMap")                    public CoreClassField coefMap;
  @Dependency(module = "Algebra.Ordered", name = "OrderedAAlgebra.coef_<")              CoreClassField coefMapL;
  @Dependency(module = "Algebra.Ordered", name = "OrderedAAlgebra.coef_<=")             CoreFunctionDefinition coefMapLE;

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
