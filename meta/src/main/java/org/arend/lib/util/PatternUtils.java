package org.arend.lib.util;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcretePattern;
import org.arend.ext.core.body.CorePattern;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.variable.VariableRenamerFactory;

import java.util.ArrayList;
import java.util.List;

public class PatternUtils {
  public static ConcretePattern toConcrete(CorePattern pattern, VariableRenamerFactory renamer, ConcreteFactory factory) {
    if (pattern.isAbsurd()) {
      return factory.tuplePattern();
    }

    CoreBinding binding = pattern.getBinding();
    if (binding != null) {
      return factory.refPattern(factory.local(renamer.getNameFromBinding(binding, null)), null);
    }

    List<ConcretePattern> subpatterns = new ArrayList<>();
    for (CorePattern subPattern : pattern.getSubPatterns()) {
      subpatterns.add(toConcrete(subPattern, renamer, factory));
    }

    CoreDefinition def = pattern.getDefinition();
    return def == null ? factory.tuplePattern(subpatterns) : factory.conPattern(def.getRef(), subpatterns);
  }

  public static boolean refines(CorePattern pattern1, CorePattern pattern2) {
    return pattern2.getBinding() != null || pattern1.isAbsurd() && pattern2.isAbsurd() || pattern1.getDefinition() == pattern2.getDefinition() && refines(pattern1.getSubPatterns(), pattern2.getSubPatterns());
  }

  public static boolean refines(List<? extends CorePattern> patterns1, List<? extends CorePattern> patterns2) {
    if (patterns1.size() != patterns2.size()) {
      return false;
    }

    for (int i = 0; i < patterns1.size(); i++) {
      if (!refines(patterns1.get(i), patterns2.get(i))) {
        return false;
      }
    }

    return true;
  }
}
