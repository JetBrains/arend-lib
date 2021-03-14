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
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.level.CoreSort;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.variable.VariableRenamerFactory;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Pair;

import java.util.*;

public class PatternUtils {
  public static ConcretePattern toConcrete(CorePattern pattern, VariableRenamerFactory renamer, ConcreteFactory factory, Map<CoreBinding, ArendRef> bindings) {
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

    List<ConcretePattern> subpatterns = toConcrete(pattern.getSubPatterns(), renamer, factory, bindings);
    CoreDefinition def = pattern.getConstructor();
    return def == null ? factory.tuplePattern(subpatterns) : factory.conPattern(def.getRef(), subpatterns);
  }

  public static List<ConcretePattern> toConcrete(Collection<? extends CorePattern> patterns, VariableRenamerFactory renamer, ConcreteFactory factory, Map<CoreBinding, ArendRef> bindings) {
    List<ConcretePattern> result = new ArrayList<>(patterns.size());
    for (CorePattern pattern : patterns) {
      result.add(toConcrete(pattern, renamer, factory, bindings));
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
  public static CoreExpression eval(CoreElimBody body, CoreSort sort, List<? extends CorePattern> patterns, List<? extends TypedExpression> removedArgs, ExpressionTypechecker typechecker, StdExtension ext, ConcreteFactory factory, Map<CoreBinding, ArendRef> bindings) {
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
        return (CoreExpression) typechecker.substituteAbstractedExpression(expr, sort, args);
      }
    }
    return null;
  }


  /**
   * Checks coverage for a list of patterns with {@code type} as their type.
   */
  private static boolean checkCoverage(List<Pair<Integer, CorePattern>> patterns, CoreExpression type, Set<Integer> result) {
    for (Pair<Integer, CorePattern> pair : patterns) {
      if (pair.proj2.isAbsurd() || pair.proj2.getBinding() != null || pair.proj2.getConstructor() instanceof CoreFunctionDefinition) {
        result.add(pair.proj1);
        return true;
      }
    }

    type = type.normalize(NormalizationMode.WHNF);

    if (patterns.isEmpty()) {
      if (!(type instanceof CoreDataCallExpression)) {
        return false;
      }
      List<CoreConstructor> constructors = ((CoreDataCallExpression) type).computeMatchedConstructors();
      return constructors != null && constructors.isEmpty();
    }

    boolean isTuple = patterns.get(0).proj2.getConstructor() == null;
    for (Pair<Integer, CorePattern> pair : patterns) {
      if (isTuple != (pair.proj2.getConstructor() == null)) {
        return false;
      }
    }

    if (isTuple) {
      CoreParameter parameters;
      if (type instanceof CoreSigmaExpression) {
        parameters = ((CoreSigmaExpression) type).getParameters();
      } else if (type instanceof CoreClassCallExpression) {
        parameters = ((CoreClassCallExpression) type).getClassFieldParameters();
      } else {
        return false;
      }
      return checkCoverage(patterns, parameters, result);
    }

    if (!(type instanceof CoreDataCallExpression)) {
      return false;
    }

    List<CoreDataCallExpression.ConstructorWithDataArguments> constructors = ((CoreDataCallExpression) type).computeMatchedConstructorsWithDataArguments();
    if (constructors == null) {
      return false;
    }

    Map<CoreDefinition, List<Pair<Integer, CorePattern>>> map = new HashMap<>();
    for (Pair<Integer, CorePattern> pair : patterns) {
      map.computeIfAbsent(pair.proj2.getConstructor(), k -> new ArrayList<>()).add(pair);
    }

    for (CoreDataCallExpression.ConstructorWithDataArguments conCall : constructors) {
      List<Pair<Integer, CorePattern>> list = map.get(conCall.getConstructor());
      if (list == null || !checkCoverage(list, conCall.getParameters(), result)) {
        return false;
      }
    }

    return true;
  }

  private static boolean checkCoverage(List<Pair<Integer, CorePattern>> rows, CoreParameter parameters, Set<Integer> result) {
    int numberOfColumns = rows.get(0).proj2.getSubPatterns().size();
    for (Pair<Integer, CorePattern> row : rows) {
      if (row.proj2.getSubPatterns().size() != numberOfColumns) {
        return false;
      }
    }

    CoreParameter param = parameters;
    for (int i = 0; i < numberOfColumns; i++) {
      if (!param.hasNext()) {
        return false;
      }
      List<Pair<Integer, CorePattern>> column = new ArrayList<>(rows.size());
      for (Pair<Integer, CorePattern> row : rows) {
        column.add(new Pair<>(row.proj1, row.proj2.getSubPatterns().get(i)));
      }
      if (!checkCoverage(column, param.getTypeExpr(), result)) {
        return false;
      }
      param = param.getNext();
    }

    if (param.hasNext()) {
      return false;
    }

    if (numberOfColumns == 0) {
      result.add(rows.get(0).proj1);
    }
    return true;
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

    int coveringIndex = -1;
    Map<CoreBinding, List<Pair<Integer, CorePattern>>> substs = new HashMap<>();
    for (int i = 0; i < actualRows.size(); i++) {
      Map<CoreBinding, CorePattern> subst = new HashMap<>();
      if (unify(actualRows.get(i), row, null, subst)) {
        if (coveringIndex == -1) {
          coveringIndex = i;
        }
        for (Map.Entry<CoreBinding, CorePattern> entry : subst.entrySet()) {
          substs.computeIfAbsent(entry.getKey(), k -> new ArrayList<>()).add(new Pair<>(i, entry.getValue()));
        }
      }
    }

    if (coveringIndex == -1) {
      return null;
    }
    if (substs.isEmpty()) {
      return Collections.singletonList(coveringIndex);
    }

    Set<Integer> coveringIndices = new HashSet<>();
    for (Map.Entry<CoreBinding, List<Pair<Integer, CorePattern>>> entry : substs.entrySet()) {
      if (!checkCoverage(entry.getValue(), entry.getKey().getTypeExpr(), coveringIndices)) {
        return null;
      }
    }

    List<Integer> coveringList = new ArrayList<>();
    for (int i = 0; i < actualRows.size(); i++) {
      if (coveringIndices.contains(i)) {
        coveringList.add(i);
      }
    }
    return coveringList;
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
