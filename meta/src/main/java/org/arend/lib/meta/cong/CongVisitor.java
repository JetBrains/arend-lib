package org.arend.lib.meta.cong;

import org.arend.ext.ArendPrelude;
import org.arend.ext.concrete.ConcreteClassElement;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Supplier;

public class CongVisitor extends BaseCoreExpressionVisitor<CongVisitor.ParamType, CongVisitor.Result> {
  private final ArendPrelude prelude;
  private final ConcreteFactory factory;
  private final ExpressionTypechecker typechecker;
  private final ConcreteSourceNode marker;
  private final List<ConcreteExpression> arguments;
  private final ConcreteReferenceExpression iRef;
  public int index = 0;

  public static class Result {
    private ConcreteExpression expression;

    public Result(ConcreteExpression expression) {
      this.expression = expression;
    }

    ConcreteExpression getExpression(CoreExpression expr, ConcreteFactory factory) {
      if (expression == null) {
        expression = factory.core(expr.computeTyped());
      }
      return expression;
    }
  }

  public static class ParamType {
    final Supplier<Result> expectedType;
    final CoreExpression other;

    public ParamType(Supplier<Result> expectedType, CoreExpression other) {
      this.expectedType = expectedType;
      this.other = other;
    }
  }

  public CongVisitor(ArendPrelude prelude, ConcreteFactory factory, ExpressionTypechecker typechecker, ConcreteSourceNode marker, List<ConcreteExpression> arguments, ArendRef iParam) {
    this.prelude = prelude;
    this.factory = factory;
    this.typechecker = typechecker;
    this.marker = marker;
    this.arguments = arguments;
    iRef = factory.ref(iParam);
  }

  @Override
  protected Result visit(CoreExpression expr1, CongVisitor.ParamType param) {
    CoreExpression other = param.other.getUnderlyingExpression();
    if (typechecker.compare(expr1, other, CMP.EQ, marker, false, true, true)) {
      return new Result(null);
    } else {
      if (index++ >= arguments.size()) {
        return null;
      } else {
        Result typeArg = param.expectedType.get();
        ConcreteExpression arg = arguments.get(index - 1);
        if (typeArg != null) {
          ConcreteExpression arg1 = expr1 instanceof CoreIntegerExpression ? factory.number(((CoreIntegerExpression) expr1).getBigInteger()) : factory.core(expr1.computeTyped());
          ConcreteExpression arg2 = other instanceof CoreIntegerExpression ? factory.number(((CoreIntegerExpression) other).getBigInteger()) : factory.core(other.computeTyped());
          arg = factory.typed(arg, typeArg.expression != null
            ? factory.app(factory.ref(prelude.getPathRef()), true, Arrays.asList(typeArg.expression, arg1, arg2))
            : factory.app(factory.ref(prelude.getEqualityRef()), true, Arrays.asList(arg1, arg2)));
        }
        return new Result(factory.app(factory.ref(prelude.getAtRef()), true, Arrays.asList(arg, iRef)));
      }
    }
  }

  private boolean findFreeVar(CoreParameter parameter, CoreBinding binding) {
    for (; parameter.hasNext(); parameter = parameter.getNext()) {
      if (parameter.getTypeExpr().findFreeBinding(binding)) {
        typechecker.getErrorReporter().report(new TypecheckingError("'cong' does not support dependent functions", marker));
        return true;
      }
    }
    return false;
  }

  private boolean visitArgs(List<? extends CoreExpression> args1, List<? extends CoreExpression> args2, List<CoreParameter> parameters, boolean paramExplicitness, List<ConcreteArgument> resultArgs) {
    boolean abstracted = false;
    int currentIndex = 0;
    CoreParameter current = null;
    for (int i = 0; i < args1.size(); i++) {
      while (current == null || !current.hasNext()) {
        current = parameters.get(currentIndex++);
      }

      Result arg = args1.get(i).accept(this, new ParamType(() -> new Result(null), args2.get(i)));
      if (arg != null) {
        boolean ok = true;
        if (arg.expression != null) {
          abstracted = true;
          if (findFreeVar(current.getNext(), current.getBinding())) {
            ok = false;
          }
          for (int j = currentIndex; j < parameters.size(); j++) {
            if (findFreeVar(parameters.get(j), current.getBinding())) {
              ok = false;
              break;
            }
          }
        }
        if (ok) {
          resultArgs.add(factory.arg(arg.getExpression(args1.get(i), factory), paramExplicitness && current.isExplicit()));
        }
      }

      current = current.getNext();
    }
    return abstracted;
  }

  private Result visitInteger(CoreConCallExpression conCall1, CoreIntegerExpression expr2, boolean reversed) {
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
    Result arg = arg1.accept(this, new ParamType(() -> new Result(null), arg2));
    return arg == null ? null : arg.expression != null ? new Result(factory.app(factory.ref(prelude.getPlusRef()), true, Arrays.asList(arg.getExpression(arg1, factory), factory.number(s)))) : new Result(null);
  }

  @Override
  public Result visitInteger(@NotNull CoreIntegerExpression expr, ParamType param) {
    CoreExpression other = param.other.getUnderlyingExpression();
    return other instanceof CoreConCallExpression && ((CoreConCallExpression) other).getDefinition() == prelude.getSuc() ? visitInteger((CoreConCallExpression) other, expr, true) : visit(expr, param);
  }

  @Override
  public Result visitConCall(@NotNull CoreConCallExpression conCall1, ParamType param) {
    CoreExpression other = param.other.getUnderlyingExpression();
    if (conCall1.getDefinition() == prelude.getSuc() && other instanceof CoreIntegerExpression) {
      return visitInteger(conCall1, (CoreIntegerExpression) other, false);
    }

    if (!(other instanceof CoreConCallExpression conCall2)) {
      return visit(conCall1, param);
    }

    if (conCall1.getDefinition() != conCall2.getDefinition()) {
      return visit(conCall1, param);
    }

    List<ConcreteArgument> args = new ArrayList<>();
    boolean abstracted = visitArgs(conCall1.getDataTypeArguments(), conCall2.getDataTypeArguments(), Collections.singletonList(conCall1.getDefinition().getDataTypeParameters()), false, args);
    abstracted = visitArgs(conCall1.getDefCallArguments(), conCall2.getDefCallArguments(), Collections.singletonList(conCall1.getDefinition().getParameters()), true, args) || abstracted;
    return args.size() == conCall1.getDataTypeArguments().size() + conCall1.getDefCallArguments().size() ? new Result(abstracted ? factory.app(factory.ref(conCall1.getDefinition().getRef()), args) : null) : null;
  }

  @Override
  public Result visitPath(@NotNull CorePathExpression expr, ParamType param) {
    CoreExpression other = param.other.getUnderlyingExpression();
    if (!(other instanceof CorePathExpression path2)) {
      return visit(expr, param);
    }

    Result arg = expr.getArgumentType().accept(this, new ParamType(() -> new Result(null), path2.getArgumentType()));
    if (arg == null) return null;
    Result result = expr.getArgument().accept(this, new ParamType(() -> new Result(null), path2.getArgument()));
    return result == null ? null : new Result(arg.expression == null || result.expression == null ? null : factory.path(result.expression));
  }

  @Override
  public Result visitAt(@NotNull CoreAtExpression expr, ParamType param) {
    CoreExpression other = param.other.getUnderlyingExpression();
    if (!(other instanceof CoreAtExpression atExpr2)) {
      return visit(expr, param);
    }
    Result pathArg = expr.getPathArgument().accept(this, new ParamType(() -> new Result(null), atExpr2.getPathArgument()));
    if (pathArg == null) return null;
    Result intervalArg = expr.getIntervalArgument().accept(this, new ParamType(() -> new Result(null), atExpr2.getIntervalArgument()));
    return intervalArg == null ? null : new Result(pathArg.expression == null || intervalArg.expression == null ? null : factory.at(pathArg.expression, intervalArg.expression));
  }

  private Result visitDefCall(@NotNull CoreDefCallExpression defCall1, ParamType param) {
    CoreExpression other = param.other.getUnderlyingExpression();
    if (!(other instanceof CoreDefCallExpression defCall2) || defCall1.getDefinition() != defCall2.getDefinition()) {
      return visit(defCall1, param);
    }

    List<ConcreteArgument> args = new ArrayList<>();
    boolean abstracted = visitArgs(defCall1.getDefCallArguments(), defCall2.getDefCallArguments(), Collections.singletonList(defCall1.getDefinition().getParameters()), true, args);
    return args.size() == defCall1.getDefCallArguments().size() ? new Result(abstracted ? factory.app(factory.ref(defCall1.getDefinition().getRef()), args) : null) : null;
  }

  @Override
  public Result visitFunCall(@NotNull CoreFunCallExpression expr, ParamType param) {
    return visitDefCall(expr, param);
  }

  @Override
  public Result visitDataCall(@NotNull CoreDataCallExpression expr, ParamType param) {
    return visitDefCall(expr, param);
  }

  @Override
  public Result visitClassCall(@NotNull CoreClassCallExpression expr, ParamType param) {
    CoreExpression otherExpr = param.other.getUnderlyingExpression();
    if (!(otherExpr instanceof CoreClassCallExpression other) || expr.getDefinition() != other.getDefinition() || expr.getImplementations().size() != other.getImplementations().size()) {
      return visit(expr, param);
    }

    List<ConcreteClassElement> args = new ArrayList<>();
    boolean abstracted = false;
    Set<CoreClassField> fieldsToCheck = new HashSet<>();
    for (Map.Entry<? extends CoreClassField, ? extends CoreExpression> entry : expr.getImplementations()) {
      if (entry.getKey().isProperty()) continue;
      CoreExpression otherImpl = other.getAbsImplementationHere(entry.getKey());
      if (otherImpl == null) {
        return visit(expr, param);
      }
      Result arg = entry.getValue().accept(this, new ParamType(() -> new Result(null), otherImpl));
      if (arg != null) {
        if (arg.expression != null) {
          abstracted = true;
          fieldsToCheck.add(entry.getKey());
        }
        args.add(factory.implementation(entry.getKey().getRef(), arg.getExpression(entry.getValue(), factory)));
      }
    }

    if (!fieldsToCheck.isEmpty()) {
      boolean check = false;
      for (Map.Entry<? extends CoreClassField, ? extends CoreExpression> entry : expr.getImplementations()) {
        if (!check) {
          check = true;
          continue;
        }
        if (entry.getKey().getResultType().processSubexpression(subexpr -> subexpr instanceof CoreFieldCallExpression && fieldsToCheck.contains(((CoreFieldCallExpression) subexpr).getDefinition()) ? CoreExpression.FindAction.STOP : CoreExpression.FindAction.CONTINUE)) {
          return null;
        }
      }
    }

    return new Result(abstracted ? factory.classExt(factory.ref(expr.getDefinition().getRef()), args) : null);
  }

  @Override
  public Result visitTuple(@NotNull CoreTupleExpression expr, ParamType param) {
    CoreExpression otherExpr = param.other.getUnderlyingExpression();
    if (!(otherExpr instanceof CoreTupleExpression other)) {
      return visit(expr, param);
    }
    List<ConcreteArgument> args = new ArrayList<>();
    boolean abstracted = visitArgs(expr.getFields(), other.getFields(), Collections.singletonList(expr.getSigmaType().getParameters()), true, args);
    if (args.size() != expr.getFields().size()) {
      return null;
    }
    List<ConcreteExpression> fields = new ArrayList<>(args.size());
    for (ConcreteArgument arg : args) {
      fields.add(arg.getExpression());
    }
    return new Result(abstracted ? factory.tuple(fields) : null);
  }

  @Override
  public Result visitProj(@NotNull CoreProjExpression expr, ParamType param) {
    CoreExpression otherExpr = param.other.getUnderlyingExpression();
    if (!(otherExpr instanceof CoreProjExpression other) || expr.getField() != other.getField()) {
      return visit(expr, param);
    }

    Result result = expr.getExpression().accept(this, new ParamType(() -> new Result(null), other.getExpression()));
    return result == null || result.expression == null ? result : new Result(factory.proj(result.expression, expr.getField()));
  }

  @Override
  public Result visitTypeConstructor(@NotNull CoreTypeConstructorExpression expr, ParamType param) {
    CoreExpression otherExpr = param.other.getUnderlyingExpression();
    return otherExpr instanceof CoreTypeConstructorExpression ? expr.getArgument().accept(this, new ParamType(() -> new Result(null), ((CoreTypeConstructorExpression) otherExpr).getArgument())) : visit(expr, param);
  }

  @Override
  public Result visitTypeDestructor(@NotNull CoreTypeDestructorExpression expr, ParamType param) {
    CoreExpression otherExpr = param.other.getUnderlyingExpression();
    return otherExpr instanceof CoreTypeDestructorExpression ? expr.getArgument().accept(this, new ParamType(() -> new Result(null), ((CoreTypeDestructorExpression) otherExpr).getArgument())) : visit(expr, param);
  }

  @Override
  public Result visitNew(@NotNull CoreNewExpression expr, ParamType param) {
    CoreExpression otherExpr = param.other.getUnderlyingExpression();
    if (!(otherExpr instanceof CoreNewExpression)) {
      return visit(expr, param);
    }
    Result result = visitClassCall(expr.getClassCall(), new ParamType(() -> new Result(null), ((CoreNewExpression) otherExpr).getClassCall()));
    return result == null || result.expression == null ? result : new Result(factory.newExpr(result.expression));
  }

  @Override
  public Result visitApp(@NotNull CoreAppExpression expr, ParamType parameter) {
    CoreExpression other = parameter.other.getUnderlyingExpression();
    if (!(other instanceof CoreAppExpression)) {
      return visit(expr, parameter);
    }

    List<CoreExpression> args1 = new ArrayList<>();
    List<CoreExpression> args2 = new ArrayList<>();
    CoreExpression expr1 = expr;
    CoreExpression expr2 = other;
    while (expr1 instanceof CoreAppExpression && expr2 instanceof CoreAppExpression) {
      args1.add(((CoreAppExpression) expr1).getArgument());
      args2.add(((CoreAppExpression) expr2).getArgument());
      expr1 = ((CoreAppExpression) expr1).getFunction();
      expr2 = ((CoreAppExpression) expr2).getFunction();
    }

    if (!typechecker.compare(expr1, expr2, CMP.EQ, marker, false, true, true)) {
      return visit(expr, parameter);
    }

    CoreExpression type = expr1.computeType().normalize(NormalizationMode.WHNF);
    List<CoreParameter> parameters = new ArrayList<>();
    int s = 0;
    while (type instanceof CorePiExpression) {
      CoreParameter params = ((CorePiExpression) type).getParameters();
      parameters.add(params);
      s += Utils.parametersSize(params);
      if (s >= args1.size()) break;
      type = ((CorePiExpression) type).getCodomain();
    }

    if (s < args1.size()) {
      return visit(expr, parameter);
    }

    Collections.reverse(args1);
    Collections.reverse(args2);
    List<ConcreteArgument> args = new ArrayList<>();
    boolean abstracted = visitArgs(args1, args2, parameters, true, args);
    return args.size() == args1.size() ? new Result(abstracted ? factory.app(factory.core(expr1.computeTyped()), args) : null) : null;
  }

  @Override
  public Result visitArray(@NotNull CoreArrayExpression expr, ParamType parameter) {
    CoreExpression other = parameter.other.getUnderlyingExpression();
    if (!(other instanceof CoreArrayExpression array2) || !(expr.getElements().size() == array2.getElements().size() && (expr.getTail() == null) == (array2.getTail() == null) && typechecker.compare(expr.getElementsType(), array2.getElementsType(), CMP.EQ, marker, false, true, false))) {
      return visit(expr, parameter);
    }

    boolean abstracted = false;
    List<ConcreteExpression> elements = new ArrayList<>();
    for (int i = 0; i < expr.getElements().size(); i++) {
      Result argResult = expr.getElements().get(i).accept(this, new ParamType(() -> new Result(null), array2.getElements().get(i)));
      if (argResult == null) return null;
      if (argResult.expression != null) {
        abstracted = true;
      }
      elements.add(argResult.getExpression(expr.getElements().get(i), factory));
    }
    ConcreteExpression tail;
    if (expr.getTail() != null) {
      Result tailResult = expr.getTail().accept(this, new ParamType(() -> new Result(null), array2.getTail()));
      if (tailResult == null) return null;
      if (tailResult.expression != null) {
        abstracted = true;
      }
      tail = tailResult.getExpression(expr.getTail(), factory);
    } else {
      tail = null;
    }
    if (!abstracted) {
      return new Result(null);
    }

    ConcreteExpression result = tail != null ? tail : factory.ref(prelude.getEmptyArrayRef());
    for (int i = elements.size() - 1; i >= 0; i--) {
      result = factory.app(factory.ref(prelude.getArrayConsRef()), true, Arrays.asList(elements.get(i), result));
    }
    return new Result(result);
  }
}
