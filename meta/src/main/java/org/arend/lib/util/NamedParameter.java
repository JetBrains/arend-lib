package org.arend.lib.util;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ResolvedApplication;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.NameResolverError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.reference.Precedence;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;

import java.util.*;
import java.util.function.BiFunction;

public class NamedParameter {
  private final List<ArendRef> allRefs = new ArrayList<>();
  private final List<ArendRef> nonFlagRefs = new ArrayList<>();
  private final Map<ArendRef, BiFunction<ExpressionResolver, ConcreteExpression, ConcreteExpression>> handlers = new HashMap<>();
  private final ConcreteFactory factory;
  private final StdExtension ext;

  public NamedParameter(ConcreteFactory factory, StdExtension ext) {
    this.factory = factory;
    this.ext = ext;
  }

  public ArendRef add(String name) {
    ArendRef ref = factory.global(name, Precedence.DEFAULT);
    allRefs.add(ref);
    nonFlagRefs.add(ref);
    return ref;
  }

  public ArendRef add(String name, BiFunction<ExpressionResolver, ConcreteExpression, ConcreteExpression> handler) {
    ArendRef ref = factory.global(name, Precedence.DEFAULT);
    allRefs.add(ref);
    nonFlagRefs.add(ref);
    handlers.put(ref, handler);
    return ref;
  }

  public ArendRef addFlag(String name) {
    ArendRef ref = factory.global(name, Precedence.DEFAULT);
    allRefs.add(ref);
    return ref;
  }

  public ConcreteExpression resolve(ExpressionResolver resolver, ConcreteExpression expression, boolean allowMultiple) {
    assert !allRefs.isEmpty();

    if (allowMultiple && expression instanceof ConcreteTupleExpression) {
      List<ConcreteExpression> newFields = new ArrayList<>();
      for (ConcreteExpression field : ((ConcreteTupleExpression) expression).getFields()) {
        ConcreteExpression newField = resolve(resolver, field, false);
        if (newField != null) newFields.add(newField);
      }
      return factory.withData(expression.getData()).tuple(newFields);
    }

    if (!nonFlagRefs.isEmpty()) {
      ConcreteUnparsedSequenceExpression seqExpr = expression instanceof ConcreteUnparsedSequenceExpression seqExpr2 ? seqExpr2 : null;
      ResolvedApplication resolvedApp = seqExpr != null ? resolver.useRefs(Collections.singletonList(ext.casesMeta.argRef), true).resolveApplication(seqExpr) : null;
      if (resolvedApp != null && resolvedApp.leftElements() != null && resolvedApp.rightElements() != null && resolvedApp.function() instanceof ConcreteReferenceExpression refExpr && refExpr.getReferent() == ext.prelude.getEquality().getRef()) {
        ConcreteFactory factory = this.factory.withData(expression.getData());
        ConcreteExpression resolved = resolver.useRefs(nonFlagRefs, false).resolve(factory.unparsedSequence(resolvedApp.leftElements(), null));
        ArendRef resolvedRef = resolved instanceof ConcreteReferenceExpression ? ((ConcreteReferenceExpression) resolved).getReferent() : null;
        if (resolvedRef != null && nonFlagRefs.contains(resolvedRef)) {
          var handler = handlers.get(resolvedRef);
          ConcreteExpression right = factory.unparsedSequence(resolvedApp.rightElements(), seqExpr.getClauses());
          ConcreteExpression result = handler != null ? handler.apply(resolver, right) : resolver.resolve(right);
          return result == null ? null : factory.withData(expression.getData()).app(factory.withData(resolved.getData()).ref(resolvedRef), true, Collections.singletonList(result));
        }
      }
    }

    if (expression instanceof ConcreteReferenceExpression) {
      ConcreteExpression result = resolver.useRefs(allRefs, false).resolve(expression);
      if (result instanceof ConcreteReferenceExpression && nonFlagRefs.contains(((ConcreteReferenceExpression) result).getReferent())) {
        resolver.getErrorReporter().report(new NameResolverError("Expected '=' after '" + ((ConcreteReferenceExpression) result).getReferent().getRefName() + "'", expression));
        return null;
      }
      return result;
    }

    String message;
    if (allRefs.size() > 1) {
      StringBuilder builder = new StringBuilder();
      builder.append("Expected one of the following parameters: ");
      for (int i = 0; i < allRefs.size(); i++) {
        if (i > 0) {
          builder.append(", ");
        }
        builder.append(allRefs.get(i).getRefName());
      }
      message = builder.toString();
    } else {
      message = "Expected '" + allRefs.get(0).getRefName() + "'";
    }
    resolver.getErrorReporter().report(new NameResolverError(message, expression));
    return null;
  }

  public Pair<ArendRef, ConcreteExpression> getKeyAndValue(ConcreteExpression expression) {
    if (expression instanceof ConcreteAppExpression && ((ConcreteAppExpression) expression).getFunction() instanceof ConcreteReferenceExpression && nonFlagRefs.contains(((ConcreteReferenceExpression) ((ConcreteAppExpression) expression).getFunction()).getReferent())) {
      return new Pair<>(((ConcreteReferenceExpression) ((ConcreteAppExpression) expression).getFunction()).getReferent(), ((ConcreteAppExpression) expression).getArguments().get(0).getExpression());
    }
    if (expression instanceof ConcreteReferenceExpression && allRefs.contains(((ConcreteReferenceExpression) expression).getReferent())) {
      return new Pair<>(((ConcreteReferenceExpression) expression).getReferent(), null);
    }
    return null;
  }

  public void getAllValues(ConcreteExpression expression, Map<ArendRef, ConcreteExpression> parameters, Set<ArendRef> flags, List<ConcreteExpression> expressions, ErrorReporter errorReporter) {
    List<? extends ConcreteExpression> fields = expression instanceof ConcreteTupleExpression ? ((ConcreteTupleExpression) expression).getFields() : Collections.singletonList(expression);
    for (ConcreteExpression field : fields) {
      Pair<ArendRef, ConcreteExpression> pair = getKeyAndValue(field);
      if (pair != null) {
        boolean ok;
        if (pair.proj2 == null) {
          ok = flags == null || flags.add(pair.proj1);
        } else {
          ok = parameters == null || parameters.putIfAbsent(pair.proj1, pair.proj2) == null;
        }
        if (!ok && errorReporter != null) {
          errorReporter.report(new TypecheckingError((pair.proj2 == null ? "Flag" : "Parameter") + " '" + pair.proj1.getRefName() + "' is already set", field));
        }
      } else if (expressions != null) {
        expressions.add(field);
      }
    }
  }

  public boolean containsKey(ConcreteExpression expression, ArendRef param) {
    List<? extends ConcreteExpression> fields = expression instanceof ConcreteTupleExpression ? ((ConcreteTupleExpression) expression).getFields() : Collections.singletonList(expression);
    for (ConcreteExpression field : fields) {
      Pair<ArendRef, ConcreteExpression> pair = getKeyAndValue(field);
      if (pair != null && pair.proj1 == param) {
        return true;
      }
    }
    return false;
  }

  public ConcreteExpression getValue(ConcreteExpression expression, ArendRef param) {
    List<? extends ConcreteExpression> fields = expression instanceof ConcreteTupleExpression ? ((ConcreteTupleExpression) expression).getFields() : Collections.singletonList(expression);
    for (ConcreteExpression field : fields) {
      Pair<ArendRef, ConcreteExpression> pair = getKeyAndValue(field);
      if (pair != null && pair.proj1 == param) {
        return pair.proj2;
      }
    }
    return null;
  }
}
