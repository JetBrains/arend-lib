package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteAppBuilder;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.NameResolverError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.reference.Precedence;
import org.arend.ext.typechecking.*;
import org.arend.lib.StdExtension;
import org.arend.lib.util.NamedParameter;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class CasesMeta extends BaseMetaDefinition implements MetaResolver {
  private final StdExtension ext;
  final NamedParameter parameter;
  final ArendRef argRef;
  final ArendRef nameRef;
  final ArendRef searchRef;
  final ArendRef addPathRef;

  public CasesMeta(StdExtension ext) {
    this.ext = ext;
    parameter = new NamedParameter(ext.factory);
    argRef = ext.factory.global("arg", new Precedence(Precedence.Associativity.NON_ASSOC, (byte) 0, true));

    nameRef = parameter.add("name", (resolver, args) -> {
      if (args.size() == 1 && args.get(0).isExplicit() && args.get(0).getExpression() instanceof ConcreteReferenceExpression) {
        ConcreteFactory factory = ext.factory.withData(args.get(0).getExpression().getData());
        ArendRef ref = factory.localDeclaration(((ConcreteReferenceExpression) args.get(0).getExpression()).getReferent());
        resolver.registerDeclaration(ref);
        return factory.ref(ref);
      } else {
        resolver.getErrorReporter().report(new NameResolverError("Expected an identifier", args.get(0).getExpression()));
        return null;
      }
    });

    searchRef = parameter.addFlag("search");
    addPathRef = parameter.addFlag("addPath");
  }

  @Override
  public @Nullable boolean[] argumentExplicitness() {
    return new boolean[] { true, true, true };
  }

  @Override
  public int numberOfOptionalExplicitArguments() {
    return 1;
  }

  @Override
  public boolean requireExpectedType() {
    return true;
  }

  private ConcreteExpression resolveArgRef(ExpressionResolver resolver, ConcreteExpression expression) {
    return expression instanceof ConcreteReferenceExpression ? resolver.useRefs(Collections.singletonList(argRef), true).resolve(expression) : null;
  }

  private ConcreteExpression resolveArgument(ExpressionResolver resolver, ConcreteExpression argument) {
    if (argument instanceof ConcreteTupleExpression) {
      List<ConcreteExpression> newFields = new ArrayList<>();
      for (ConcreteExpression field : ((ConcreteTupleExpression) argument).getFields()) {
        ConcreteExpression newField = resolveArgument1(resolver, field);
        newFields.add(newField);
        if (newField instanceof ConcreteAppExpression && ((ConcreteAppExpression) newField).getFunction() instanceof ConcreteReferenceExpression && ((ConcreteReferenceExpression) ((ConcreteAppExpression) newField).getFunction()).getReferent() == argRef) {
          ConcreteExpression name = parameter.getValue(((ConcreteAppExpression) newField).getArguments().get(1).getExpression(), nameRef);
          if (name instanceof ConcreteReferenceExpression) {
            resolver = resolver.useRefs(Collections.singletonList(((ConcreteReferenceExpression) name).getReferent()), true);
          }
        }
      }
      return ext.factory.withData(argument.getData()).tuple(newFields);
    } else {
      return resolveArgument1(resolver, argument);
    }
  }

  private ConcreteExpression addType(ConcreteExpression expr, ConcreteExpression type, ConcreteExpression opArg) {
    if (type == null) return expr;
    ConcreteFactory factory = ext.factory.withData(expr.getData());
    return factory.app(opArg != null ? opArg : factory.ref(argRef), true, Arrays.asList(expr, factory.tuple(), type));
  }

  private ConcreteExpression resolveArgument1(ExpressionResolver resolver, ConcreteExpression argument) {
    ConcreteExpression type = argument instanceof ConcreteTypedExpression ? resolver.resolve(((ConcreteTypedExpression) argument).getType()) : null;
    if (argument instanceof ConcreteTypedExpression) argument = ((ConcreteTypedExpression) argument).getExpression();

    List<ConcreteArgument> sequence = argument.getArgumentsSequence();
    if (sequence.size() >= 3 && sequence.get(sequence.size() - 1).isExplicit() && sequence.get(sequence.size() - 2).isExplicit()) {
      ConcreteExpression opArg = resolveArgRef(resolver, sequence.get(sequence.size() - 2).getExpression());
      if (opArg instanceof ConcreteReferenceExpression && ((ConcreteReferenceExpression) opArg).getReferent() == argRef) {
        ConcreteExpression result = resolver.resolve(argument.getData(), sequence.subList(0, sequence.size() - 2));
        ConcreteExpression params = parameter.resolve(resolver, sequence.get(sequence.size() - 1).getExpression(), false, true);
        if (params == null && type == null) return result;
        ConcreteFactory factory = ext.factory.withData(argument.getData());
        ConcreteAppBuilder builder = factory.appBuilder(opArg).app(result).app(params != null ? params : factory.tuple());
        if (type != null) builder.app(type);
        return builder.build();
      }

      if (opArg != null) {
        sequence.set(sequence.size() - 2, ext.factory.arg(opArg, true));
        return addType(resolver.resolve(argument.getData(), sequence), type, opArg);
      }
    }

    if (sequence.size() >= 2 && sequence.get(sequence.size() - 1).isExplicit()) {
      ConcreteExpression lastArg = resolveArgRef(resolver, sequence.get(sequence.size() - 1).getExpression());
      if (lastArg instanceof ConcreteReferenceExpression && ((ConcreteReferenceExpression) lastArg).getReferent() == argRef) {
        resolver.getErrorReporter().report(new NameResolverError("Expected an argument after '" + argRef.getRefName() + "'", lastArg));
      }

      if (lastArg != null) {
        sequence.set(sequence.size() - 1, ext.factory.arg(lastArg, true));
        return addType(resolver.resolve(argument.getData(), sequence), type, lastArg);
      }
    }

    return addType(resolver.resolve(argument), type, null);
  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    if (args.size() > 2 || args.isEmpty() || !args.get(0).isExplicit() || args.size() > 1 && !args.get(1).isExplicit()) {
      resolver.getErrorReporter().report(new NameResolverError("Expected at least 1 and at most 2 explicit arguments", contextData.getMarker()));
      return null;
    }

    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    ConcreteAppBuilder builder = factory.appBuilder(contextData.getReferenceExpression())
      .app(resolveArgument(resolver, args.get(0).getExpression()), args.get(0).isExplicit())
      .app(resolver.resolve(factory.caseExpr(false, Collections.emptyList(), null, null, contextData.getClauses() == null ? Collections.emptyList() : contextData.getClauses().getClauseList())));
    if (args.size() > 1) {
      builder.app(resolver.resolve(args.get(1).getExpression()));
    }
    return builder.build();
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    List<? extends ConcreteArgument> args = contextData.getArguments();
    if (args.size() > 2) {
      typechecker.getErrorReporter().report(new TypecheckingError(GeneralError.Level.WARNING_UNUSED, "Argument is ignored", args.get(2).getExpression()));
    }

    ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
    List<? extends ConcreteExpression> caseArgExprs = Utils.getArgumentList(args.get(0).getExpression());
    List<ConcreteCaseArgument> caseArgs = new ArrayList<>(caseArgExprs.size());
    for (ConcreteExpression caseArgExpr : caseArgExprs) {
      if (caseArgExpr instanceof ConcreteAppExpression && ((ConcreteAppExpression) caseArgExpr).getFunction() instanceof ConcreteReferenceExpression && ((ConcreteReferenceExpression) ((ConcreteAppExpression) caseArgExpr).getFunction()).getReferent() == argRef) {
        List<? extends ConcreteArgument> parameters = ((ConcreteAppExpression) caseArgExpr).getArguments();
        Map<ArendRef, ConcreteExpression> params = new HashMap<>();
        Set<ArendRef> flags = new HashSet<>();
        parameter.getAllValues(parameters.get(1).getExpression(), params, flags, null, typechecker.getErrorReporter());
        boolean addPath = flags.contains(addPathRef);
        ConcreteExpression nameExpr = params.get(nameRef);
        ArendRef caseArgRef = nameExpr instanceof ConcreteReferenceExpression ? ((ConcreteReferenceExpression) nameExpr).getReferent() : addPath ? factory.local("x") : null;
        ConcreteExpression argExpr = parameters.get(0).getExpression();
        ConcreteExpression argType = parameters.size() > 2 ? parameters.get(2).getExpression() : null;
        caseArgs.add(argExpr instanceof ConcreteReferenceExpression && caseArgRef == null ? factory.caseArg((ConcreteReferenceExpression) argExpr, argType) : factory.caseArg(argExpr, caseArgRef, argType));
        if (addPath) {
          caseArgs.add(factory.caseArg(factory.ref(ext.prelude.getIdp().getRef()), null, factory.app(factory.ref(ext.prelude.getEquality().getRef()), true, Arrays.asList(factory.hole(), factory.ref(caseArgRef)))));
        }
      } else {
        caseArgs.add(caseArgExpr instanceof ConcreteReferenceExpression ? factory.caseArg((ConcreteReferenceExpression) caseArgExpr, null) : factory.caseArg(caseArgExpr, null, null));
      }
    }

    return typechecker.typecheck(factory.caseExpr(false, caseArgs, null, null, ((ConcreteCaseExpression) args.get(1).getExpression()).getClauses()), contextData.getExpectedType());
  }
}
