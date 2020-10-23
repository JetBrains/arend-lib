package org.arend.lib.meta.cong;

import org.arend.ext.ArendPrelude;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.level.CoreSort;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.lib.util.Pair;
import org.jetbrains.annotations.NotNull;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;

public class CongVisitor extends BaseCoreExpressionVisitor<Pair<Supplier<ConcreteExpression>, CoreExpression>, ConcreteExpression> {
  private final ArendPrelude prelude;
  private final ConcreteFactory factory;
  private final ExpressionTypechecker typechecker;
  private final ConcreteSourceNode marker;
  private final List<ConcreteExpression> arguments;
  private final ArendRef iParam;
  private final ConcreteReferenceExpression iRef;
  public int index = 0;

  public CongVisitor(ArendPrelude prelude, ConcreteFactory factory, ExpressionTypechecker typechecker, ConcreteSourceNode marker, List<ConcreteExpression> arguments, ArendRef iParam) {
    this.prelude = prelude;
    this.factory = factory;
    this.typechecker = typechecker;
    this.marker = marker;
    this.arguments = arguments;
    this.iParam = iParam;
    iRef = factory.ref(iParam);
  }

  @Override
  protected ConcreteExpression visit(CoreExpression expr1, Pair<Supplier<ConcreteExpression>, CoreExpression> pair) {
    if (typechecker.compare(expr1, pair.proj2, CMP.EQ, marker, false, true)) {
      return factory.core(expr1.computeTyped());
    } else {
      if (index++ >= arguments.size()) {
        return null;
      } else {
        ConcreteExpression typeArg = pair.proj1.get();
        if (typeArg == null) return null;
        return factory.app(factory.ref(prelude.getAt().getRef()), true, Arrays.asList(factory.typed(arguments.get(index - 1), factory.app(factory.ref(prelude.getPath().getRef()), true, Arrays.asList(typeArg, factory.core(expr1.computeTyped()), factory.core(pair.proj2.computeTyped())))), iRef));
      }
    }
  }

  private void visitArgs(List<? extends CoreExpression> args1, List<? extends CoreExpression> args2, CoreParameter parameter, boolean paramExplicitness, List<ConcreteArgument> resultArgs, CoreSort[] sort) {
    for (int i = 0; i < args1.size(); i++) {
      int finalI = i;
      ConcreteExpression arg = args1.get(i).accept(this, new Pair<>(() -> {
        if (finalI > resultArgs.size()) return null;
        if (sort[0] == null) sort[0] = typechecker.generateSort(marker);
        CoreParameter param = typechecker.substituteParameters(parameter, sort[0], resultArgs.subList(0, finalI).stream().map(ConcreteArgument::getExpression).collect(Collectors.toList()));
        return param == null ? null : factory.lam(Collections.singletonList(factory.param(iParam)), factory.core(param.getTypedType()));
      }, args2.get(i)));
      if (arg != null) {
        resultArgs.add(factory.arg(arg, paramExplicitness && parameter.isExplicit()));
      }
    }
  }

  private ConcreteExpression visitInteger(CoreConCallExpression conCall1, CoreIntegerExpression expr2, boolean reversed) {
    int s = 0;
    CoreExpression expr1 = conCall1;
    BigInteger n = expr2.getBigInteger();
    while (expr1 instanceof CoreConCallExpression && ((CoreConCallExpression) expr1).getDefinition() == prelude.getSuc() && !n.equals(BigInteger.ZERO)) {
      s++;
      expr1 = ((CoreConCallExpression) expr1).getDefCallArguments().get(0);
      n = n.subtract(BigInteger.ONE);
    }

    CoreExpression arg1;
    CoreExpression arg2 = Objects.requireNonNull(typechecker.typecheck(factory.number(n), null)).getExpression();
    if (reversed) {
      arg1 = arg2;
      arg2 = expr1;
    } else {
      arg1 = expr1;
    }
    ConcreteExpression arg = arg1.accept(this, new Pair<>(() -> factory.lam(Collections.singletonList(factory.param(null)), factory.ref(prelude.getNat().getRef())), arg2));
    return factory.app(factory.ref(prelude.getPlus().getRef()), true, Arrays.asList(arg, factory.number(s)));
  }

  @Override
  public ConcreteExpression visitInteger(@NotNull CoreIntegerExpression expr, Pair<Supplier<ConcreteExpression>, CoreExpression> pair) {
    return pair.proj2 instanceof CoreConCallExpression && ((CoreConCallExpression) pair.proj2).getDefinition() == prelude.getSuc() ? visitInteger((CoreConCallExpression) pair.proj2, expr, true) : visit(expr, pair);
  }

  @Override
  public ConcreteExpression visitConCall(@NotNull CoreConCallExpression conCall1, Pair<Supplier<ConcreteExpression>, CoreExpression> pair) {
    if (conCall1.getDefinition() == prelude.getSuc() && pair.proj2 instanceof CoreIntegerExpression) {
      return visitInteger(conCall1, (CoreIntegerExpression) pair.proj2, false);
    }

    if (!(pair.proj2 instanceof CoreConCallExpression)) {
      return visit(conCall1, pair);
    }

    CoreConCallExpression conCall2 = (CoreConCallExpression) pair.proj2;
    if (conCall1.getDefinition() != conCall2.getDefinition()) {
      return visit(conCall1, pair);
    }

    CoreParameter parameter = conCall1.getDefinition().getAllParameters();
    if (!parameter.hasNext()) {
      return factory.core(conCall1.computeTyped());
    }

    CoreSort[] sort = new CoreSort[1];
    List<ConcreteArgument> args = new ArrayList<>();
    visitArgs(conCall1.getDataTypeArguments(), conCall2.getDataTypeArguments(), parameter, false, args, sort);
    visitArgs(conCall1.getDefCallArguments(), conCall2.getDefCallArguments(), parameter, true, args, sort);
    return args.size() == conCall1.getDataTypeArguments().size() + conCall1.getDefCallArguments().size() ? factory.app(factory.ref(conCall1.getDefinition().getRef()), args) : null;
  }

  private ConcreteExpression visitDefCall(@NotNull CoreDefCallExpression defCall1, Pair<Supplier<ConcreteExpression>, CoreExpression> pair) {
    if (!(pair.proj2 instanceof CoreDefCallExpression)) {
      return visit(defCall1, pair);
    }

    CoreDefCallExpression defCall2 = (CoreDefCallExpression) pair.proj2;
    if (defCall1.getDefinition() != defCall2.getDefinition()) {
      return visit(defCall1, pair);
    }

    CoreSort[] sort = new CoreSort[1];
    List<ConcreteArgument> args = new ArrayList<>();
    visitArgs(defCall1.getDefCallArguments(), defCall2.getDefCallArguments(), defCall1.getDefinition().getParameters(), true, args, sort);
    return args.size() == defCall1.getDefCallArguments().size() ? factory.app(factory.ref(defCall1.getDefinition().getRef()), args) : null;
  }

  @Override
  public ConcreteExpression visitFunCall(@NotNull CoreFunCallExpression expr, Pair<Supplier<ConcreteExpression>, CoreExpression> pair) {
    return visitDefCall(expr, pair);
  }

  @Override
  public ConcreteExpression visitDataCall(@NotNull CoreDataCallExpression expr, Pair<Supplier<ConcreteExpression>, CoreExpression> pair) {
    return visitDefCall(expr, pair);
  }
}
