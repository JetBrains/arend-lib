package org.arend.lib.meta.equation.binop_matcher;

import org.arend.ext.core.definition.CoreDataDefinition;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreDefCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.lib.util.Utils;

import java.util.ArrayList;
import java.util.List;

public class DefinitionFunctionMatcher implements FunctionMatcher {
  private final CoreDefinition definition;
  private final int numberOfArguments;

  public DefinitionFunctionMatcher(CoreDefinition definition, int numberOfArguments) {
    this.definition = definition;
    this.numberOfArguments = numberOfArguments;
  }

  @Override
  public List<CoreExpression> match(CoreExpression expr) {
    List<CoreExpression> args = new ArrayList<>(numberOfArguments);
    CoreExpression function = Utils.getAppArguments(expr, numberOfArguments, args);
    if (args.size() == numberOfArguments || definition instanceof CoreFunctionDefinition || definition instanceof CoreDataDefinition) {
      function = function.normalize(NormalizationMode.WHNF);
      if (function instanceof CoreDefCallExpression && ((CoreDefCallExpression) function).getDefinition() == definition) {
        if (args.size() != numberOfArguments) {
          List<? extends CoreExpression> defCallArgs = ((CoreDefCallExpression) function).getDefCallArguments();
          if (args.size() + defCallArgs.size() == numberOfArguments) {
            args.addAll(defCallArgs);
          }
        }
        if (args.size() == numberOfArguments) {
          return args;
        }
      }
    }
    return null;
  }
}
