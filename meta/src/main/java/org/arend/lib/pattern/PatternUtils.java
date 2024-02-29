package org.arend.lib.pattern;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.pattern.ConcreteReferencePattern;
import org.arend.ext.core.body.CoreElimBody;
import org.arend.ext.core.body.CoreElimClause;
import org.arend.ext.core.body.CorePattern;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.level.LevelSubstitution;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.ext.variable.VariableRenamerFactory;
import org.arend.lib.StdExtension;

import java.util.*;

public class PatternUtils {
  private static ConcretePattern toConcrete(CorePattern pattern, VariableRenamerFactory renamer, ConcreteFactory factory, Map<CoreBinding, ArendRef> bindings) {
    if (pattern.isAbsurd()) {
      return factory.tuplePattern();
    }

    CoreBinding binding = pattern.getBinding();
    if (binding != null) {
      ArendRef ref = bindings == null ? null : bindings.get(binding);
      if (ref == null) {
        ref = factory.local(renamer.getNameFromBinding(binding, null));
        if (bindings != null) {
          bindings.put(binding, ref);
        }
      }
      return factory.refPattern(ref, null);
    }

    List<ConcretePattern> subpatterns = toConcrete(pattern.getSubPatterns(), null, renamer, factory, bindings, pattern.getParameters());
    CoreDefinition def = pattern.getConstructor();
    return def == null ? factory.tuplePattern(subpatterns) : factory.conPattern(def.getRef(), subpatterns);
  }

  public static ConcretePattern toConcrete(CorePattern pattern, VariableRenamerFactory renamer, ConcreteFactory factory, Map<CoreBinding, ArendRef> bindings, boolean isExplicit) {
    ConcretePattern result = toConcrete(pattern, renamer, factory, bindings);
    return isExplicit ? result : result.implicit();
  }

  public static List<ConcretePattern> toConcrete(List<? extends CorePattern> patterns, List<? extends ArendRef> asRefs, VariableRenamerFactory renamer, ConcreteFactory factory, Map<CoreBinding, ArendRef> bindings, CoreParameter parameters) {
    assert asRefs == null || patterns.size() == asRefs.size();
    List<ConcretePattern> result = new ArrayList<>(patterns.size());
    for (int i = 0; i < patterns.size(); i++) {
      ArendRef asRef = asRefs != null ? asRefs.get(i) : null;
      CoreBinding binding = patterns.get(i).getBinding();
      boolean setMap = binding != null && bindings == null && asRef != null;
      if (setMap) {
        bindings = Collections.singletonMap(binding, asRef);
      }
      ConcretePattern pattern = toConcrete(patterns.get(i), renamer, factory, bindings, parameters == null || !parameters.hasNext() || parameters.isExplicit());
      result.add(asRef != null && binding == null ? pattern.as(asRefs.get(i), null) : pattern);
      if (setMap) {
        bindings = null;
      }
      if (parameters != null && parameters.hasNext()) parameters = parameters.getNext();
    }
    return result;
  }

  public static ConcreteExpression toExpression(CorePattern pattern, StdExtension ext, ConcreteFactory factory, Map<CoreBinding, ArendRef> bindings) {
    CoreBinding binding = pattern.getBinding();
    if (binding != null) {
      ArendRef ref = bindings == null ? null : bindings.get(binding);
      return ref != null ? factory.ref(ref) : factory.core(binding.makeReference().computeTyped());
    }

    if (pattern.getConstructor() == null) {
      return factory.app(factory.ref(ext.constructorMetaRef), true, toExpression(pattern.getSubPatterns(), ext, factory, bindings));
    } else {
      return factory.app(factory.ref(pattern.getConstructor().getRef()), true, toExpression(pattern.getSubPatterns(), ext, factory, bindings));
    }
  }

  public static List<ConcreteExpression> toExpression(Collection<? extends CorePattern> patterns, StdExtension ext, ConcreteFactory factory, Map<CoreBinding, ArendRef> bindings) {
    List<ConcreteExpression> result = new ArrayList<>(patterns.size());
    for (CorePattern pattern : patterns) {
      result.add(toExpression(pattern, ext, factory, bindings));
    }
    return result;
  }

  public static void getReferences(Collection<? extends ConcretePattern> patterns, List<ArendRef> result) {
    for (ConcretePattern pattern : patterns) {
      if (pattern instanceof ConcreteReferencePattern) {
        result.add(((ConcreteReferencePattern) pattern).getRef());
      }
      getReferences(pattern.getPatterns(), result);
    }
  }

  public static CoreParameter getAllBindings(Collection<? extends CorePattern> patterns) {
    for (CorePattern pattern : patterns) {
      CoreParameter param = pattern.getAllBindings();
      if (param.hasNext()) {
        return param;
      }
    }
    return null;
  }

  public static int getNumberOfBindings(CorePattern pattern) {
    if (pattern.getBinding() != null) {
      return 1;
    }

    int s = 0;
    for (CorePattern subPattern : pattern.getSubPatterns()) {
      s += getNumberOfBindings(subPattern);
    }
    return s;
  }

  public static boolean isAbsurd(CorePattern pattern) {
    if (pattern.isAbsurd()) {
      return true;
    }
    for (CorePattern subPattern : pattern.getSubPatterns()) {
      if (isAbsurd(subPattern)) {
        return true;
      }
    }
    return false;
  }

  public static boolean isAbsurd(Collection<? extends CorePattern> patterns) {
    for (CorePattern pattern : patterns) {
      if (isAbsurd(pattern)) {
        return true;
      }
    }
    return false;
  }


  public static boolean isTrivial(CorePattern pattern) {
    if (pattern.getBinding() != null) {
      return true;
    }
    if (pattern.isAbsurd() || pattern.getConstructor() != null) {
      return false;
    }
    for (CorePattern subPattern : pattern.getSubPatterns()) {
      if (!isTrivial(subPattern)) {
        return false;
      }
    }
    return true;
  }

  public static boolean isTrivial(Collection<? extends CorePattern> patterns) {
    for (CorePattern pattern : patterns) {
      if (!isTrivial(pattern)) {
        return false;
      }
    }
    return true;
  }

  public static boolean refines(CorePattern pattern1, CorePattern pattern2) {
    return pattern2.getBinding() != null || pattern1.isAbsurd() && pattern2.isAbsurd() || pattern1.getConstructor() == pattern2.getConstructor() && refines(pattern1.getSubPatterns(), pattern2.getSubPatterns()) || pattern2.getBinding() != null && isTrivial(pattern1);
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


  public static boolean unify(CorePattern pattern1, CorePattern pattern2, Map<CoreBinding, CorePattern> subst1, Map<CoreBinding, CorePattern> subst2) {
    if (pattern1 == null || pattern2 == null || pattern1.isAbsurd() && pattern2.isAbsurd()) {
      return true;
    }

    if (pattern1.getBinding() != null || pattern2.getBinding() != null) {
      if (subst1 != null && pattern1.getBinding() != null) {
        subst1.put(pattern1.getBinding(), pattern2);
      }
      if (subst2 != null && pattern2.getBinding() != null) {
        subst2.put(pattern2.getBinding(), pattern1);
      }
      return true;
    }

    if (pattern1.getConstructor() != pattern2.getConstructor() || pattern1.isAbsurd() || pattern2.isAbsurd()) {
      return false;
    }

    return unify(pattern1.getSubPatterns(), pattern2.getSubPatterns(), subst1, subst2);
  }

  public static boolean unify(List<? extends CorePattern> patterns1, List<? extends CorePattern> patterns2, Map<CoreBinding, CorePattern> subst1, Map<CoreBinding, CorePattern> subst2) {
    if (patterns1.size() != patterns2.size()) {
      return false;
    }

    for (int i = 0; i < patterns1.size(); i++) {
      if (!unify(patterns1.get(i), patterns2.get(i), subst1, subst2)) {
        return false;
      }
    }

    return true;
  }


  // patterns[i] == null iff removedArgs[i] != null.
  // Moreover, if these equivalent conditions hold, then body.getClauses().get(j)[i].getBinding() != null for every j.
  public static CoreExpression eval(CoreElimBody body, LevelSubstitution levelSubst, List<? extends CorePattern> patterns, List<? extends TypedExpression> removedArgs, ExpressionTypechecker typechecker, StdExtension ext, ConcreteFactory factory, Map<CoreBinding, ArendRef> bindings) {
    loop:
    for (CoreElimClause clause : body.getClauses()) {
      Map<CoreBinding, CorePattern> subst1 = new HashMap<>();
      Map<CoreBinding, CorePattern> subst2 = new HashMap<>();
      if (unify(clause.getPatterns(), patterns, subst1, subst2)) {
        for (CorePattern value : subst2.values()) {
          if (value.getBinding() == null) {
            continue loop;
          }
        }
        AbstractedExpression expr = clause.getAbstractedExpression();
        if (expr == null) {
          return null;
        }
        CoreParameter param = getAllBindings(clause.getPatterns());
        if (param == null) {
          return (CoreExpression) expr;
        }
        Map<CoreBinding, TypedExpression> removedMap = new HashMap<>();
        for (int i = 0; i < removedArgs.size(); i++) {
          CoreBinding binding = clause.getPatterns().get(i).getBinding();
          if (removedArgs.get(i) != null && binding != null) {
            removedMap.put(binding, removedArgs.get(i));
          }
        }
        List<ConcreteExpression> args = new ArrayList<>();
        for (; param.hasNext(); param = param.getNext()) {
          TypedExpression removed = removedMap.get(param.getBinding());
          args.add(removed != null ? factory.core(removed) : toExpression(subst1.get(param.getBinding()), ext, factory, bindings));
        }
        return (CoreExpression) typechecker.substituteAbstractedExpression(expr, levelSubst, args, null);
      }
    }
    return null;
  }

  /**
   * @return indices of rows from {@code actualRows} that cover {@code row}, or {@code null} if {@code actualRows} do not cover {@code row}
   */
  public static List<Integer> computeCovering(List<? extends List<? extends CorePattern>> actualRows, List<? extends CorePattern> row) {
    for (CorePattern pattern : row) {
      if (pattern.isAbsurd()) {
        return Collections.emptyList();
      }
    }
    if (actualRows.isEmpty()) {
      return null;
    }

    List<Pair<? extends List<? extends CorePattern>, Integer>> rows = new ArrayList<>(actualRows.size());
    for (int i = 0; i < actualRows.size(); i++) {
      rows.add(new Pair<>(actualRows.get(i), i));
    }
    Set<Integer> indices = new HashSet<>();
    if (!computeCovering(rows, row, indices)) {
      return null;
    }
    List<Integer> result = new ArrayList<>(actualRows.size());
    for (int i = 0; i < actualRows.size(); i++) {
      if (indices.contains(i)) {
        result.add(i);
      }
    }
    return result;
  }

  private static boolean computeCovering(List<Pair<? extends List<? extends CorePattern>, Integer>> actualRows, List<? extends CorePattern> row, Set<Integer> indices) {
    if (actualRows.isEmpty()) {
      return false;
    }
    if (row.isEmpty()) {
      indices.add(actualRows.get(0).proj2);
      return true;
    }

    class MyBinding implements CoreBinding {
      final CoreExpression type;

      MyBinding(CoreExpression type) {
          this.type = type;
      }

      @Override
      public CoreExpression getTypeExpr() {
        return type;
      }

      @Override
      public CoreReferenceExpression makeReference() {
        return null;
      }

      @Override
      public String getName() {
        return null;
      }
    }

    CorePattern pattern = row.get(0);
    List<Pair<? extends List<? extends CorePattern>, Integer>> newRows = new ArrayList<>(actualRows.size());
    List<? extends CorePattern> rowTail = row.subList(1, row.size());
    if (pattern.getBinding() != null) {
      boolean allVars = true;
      boolean hasVars = false;
      Set<CoreDefinition> constructors = new LinkedHashSet<>();
      for (Pair<? extends List<? extends CorePattern>, Integer> actualRow : actualRows) {
        CorePattern actualPattern = actualRow.proj1.get(0);
        if (actualPattern.isAbsurd()) { // TODO: This is not needed if implemented properly; see TODO below
          indices.add(actualRow.proj2);
          return true;
        }
        if (actualPattern.getBinding() == null) {
          allVars = false;
          if (actualPattern.getConstructor() != null) {
            constructors.add(actualPattern.getConstructor());
          }
        } else {
          hasVars = true;
        }
      }

      if (allVars) {
        for (Pair<? extends List<? extends CorePattern>, Integer> actualRow : actualRows) {
          newRows.add(new Pair<>(actualRow.proj1.subList(1, actualRow.proj1.size()), actualRow.proj2));
        }
        return computeCovering(newRows, rowTail, indices);
      }

      List<Pair<CoreDefinition, CoreParameter>> consWithParams;
      CoreExpression type = pattern.getBinding().getTypeExpr();
      if (type != null) type = type.unfoldType();
      if (type instanceof CoreSigmaExpression sigmaExpr) {
        consWithParams = Collections.singletonList(new Pair<>(null, sigmaExpr.getParameters()));
      } else if (type instanceof CoreClassCallExpression classCall) {
        consWithParams = Collections.singletonList(new Pair<>(null, classCall.getClassFieldParameters()));
      } else {
        List<CoreExpression.ConstructorWithDataArguments> constructorsWithArgs = type == null ? null : type.computeMatchedConstructorsWithDataArguments();
        if (constructorsWithArgs == null) {
          // TODO: We should return null here, but to do this we need to substitute previous patterns in type
          consWithParams = new ArrayList<>(constructors.size());
          for (CoreDefinition constructor : constructors) {
            consWithParams.add(new Pair<>(constructor, constructor.getParameters()));
          }
        } else {
          if (!hasVars) {
            for (CoreExpression.ConstructorWithDataArguments cons : constructorsWithArgs) {
              if (!constructors.contains(cons.getConstructor())) {
                return false;
              }
            }
          }
          consWithParams = new ArrayList<>(constructorsWithArgs.size());
          for (CoreExpression.ConstructorWithDataArguments cons : constructorsWithArgs) {
            consWithParams.add(new Pair<>(cons.getConstructor(), cons.getParameters()));
          }
        }
      }

      for (Pair<CoreDefinition, CoreParameter> pair : consWithParams) {
        List<CorePattern> newRow = new ArrayList<>();
        for (CoreParameter param = pair.proj2; param.hasNext(); param = param.getNext()) {
          newRow.add(new ArendPattern(new MyBinding(param.getTypeExpr()), null, Collections.emptyList(), null, null));
        }
        newRow.addAll(rowTail);

        newRows.clear();
        for (Pair<? extends List<? extends CorePattern>, Integer> actualRow : actualRows) {
          CorePattern actualPattern = actualRow.proj1.get(0);
          if (actualPattern.getBinding() != null) {
            List<CorePattern> newActualRow = new ArrayList<>();
            for (CoreParameter param = pair.proj2; param.hasNext(); param = param.getNext()) {
              newActualRow.add(new ArendPattern(new MyBinding(null), null, Collections.emptyList(), null, null));
            }
            newActualRow.addAll(actualRow.proj1.subList(1, actualRow.proj1.size()));
            newRows.add(new Pair<>(newActualRow, actualRow.proj2));
          } else if (actualPattern.getConstructor() == pair.proj1) {
            List<CorePattern> newActualRow = new ArrayList<>();
            newActualRow.addAll(actualPattern.getSubPatterns());
            newActualRow.addAll(actualRow.proj1.subList(1, actualRow.proj1.size()));
            newRows.add(new Pair<>(newActualRow, actualRow.proj2));
          }
        }

        if (!computeCovering(newRows, newRow, indices)) {
          return false;
        }
      }

      return true;
    } else {
      List<CorePattern> newRow = new ArrayList<>();
      newRow.addAll(pattern.getSubPatterns());
      newRow.addAll(rowTail);

      for (Pair<? extends List<? extends CorePattern>, Integer> actualRow : actualRows) {
        CorePattern actualPattern = actualRow.proj1.get(0);
        if (actualPattern.getBinding() != null) {
          List<CorePattern> newActualRow = new ArrayList<>();
          for (CorePattern ignored : pattern.getSubPatterns()) {
            newActualRow.add(new ArendPattern(new MyBinding(null), null, Collections.emptyList(), null, null));
          }
          newActualRow.addAll(actualRow.proj1.subList(1, actualRow.proj1.size()));
          newRows.add(new Pair<>(newActualRow, actualRow.proj2));
        } else if (actualPattern.getConstructor() == pattern.getConstructor()) {
          List<CorePattern> newActualRow = new ArrayList<>();
          newActualRow.addAll(actualPattern.getSubPatterns());
          newActualRow.addAll(actualRow.proj1.subList(1, actualRow.proj1.size()));
          newRows.add(new Pair<>(newActualRow, actualRow.proj2));
        }
      }

      return computeCovering(newRows, newRow, indices);
    }
  }

  public static List<CorePattern> subst(Collection<? extends CorePattern> patterns, Map<? extends CoreBinding, ? extends CorePattern> map) {
    List<CorePattern> result = new ArrayList<>(patterns.size());
    for (CorePattern pattern : patterns) {
      result.add(pattern.subst(map));
    }
    return result;
  }

  public static List<CorePattern> replaceParameters(List<? extends CorePattern> patterns, CoreParameter parameters, VariableRenamerFactory renamer) {
    List<CorePattern> result = new ArrayList<>(patterns.size());
    for (CorePattern pattern : patterns) {
      parameters = replaceParameters(pattern, parameters, result, renamer);
    }
    return result;
  }

  public static CoreParameter replaceParameters(CorePattern pattern, CoreParameter parameters, List<CorePattern> result, VariableRenamerFactory renamer) {
    if (pattern.isAbsurd()) {
      result.add(pattern);
      return parameters;
    }

    if (pattern.getBinding() != null) {
      result.add(new ArendPattern(parameters.getBinding(), null, Collections.emptyList(), parameters, renamer));
      return parameters.getNext();
    }

    List<CorePattern> subPatterns = new ArrayList<>();
    result.add(new ArendPattern(null, pattern.getConstructor(), subPatterns, parameters, renamer));
    for (CorePattern subPattern : pattern.getSubPatterns()) {
      parameters = replaceParameters(subPattern, parameters, subPatterns, renamer);
    }
    return parameters;
  }
}
