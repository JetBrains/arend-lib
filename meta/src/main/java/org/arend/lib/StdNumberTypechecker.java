package org.arend.lib;

import org.arend.ext.LiteralTypechecker;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.CoreDataCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.instance.SubclassSearchParameters;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.util.Utils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.math.BigInteger;
import java.util.Collections;

public class StdNumberTypechecker implements LiteralTypechecker {
  private final StdExtension ext;

  public StdNumberTypechecker(StdExtension ext) {
    this.ext = ext;
  }

  @Override
  public @Nullable TypedExpression typecheckString(@NotNull String unescapedString, @NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    return null;
  }

  @Override
  public @Nullable TypedExpression typecheckNumber(@NotNull BigInteger number, @NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    CoreExpression expectedType = contextData.getExpectedType() == null ? null : contextData.getExpectedType().normalize(NormalizationMode.WHNF);
    if (expectedType != null && !(expectedType instanceof CoreDataCallExpression && (((CoreDataCallExpression) expectedType).getDefinition() == ext.prelude.getNat() || ((CoreDataCallExpression) expectedType).getDefinition() == ext.prelude.getInt()))) {
      CoreClassDefinition classDef = number.equals(BigInteger.ZERO) ? ext.equationMeta.AddPointed : number.equals(BigInteger.ONE) ? ext.equationMeta.Pointed : number.compareTo(BigInteger.ZERO) < 0 ? ext.equationMeta.Ring : ext.equationMeta.Semiring;
      TypedExpression instance = Utils.findInstance(new SubclassSearchParameters(classDef), ext.carrier, expectedType, typechecker, contextData.getMarker());
      if (instance != null) {
        ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
        ConcreteExpression cExpr;
        ConcreteExpression cInstance = factory.core(null, instance);
        if (classDef == ext.equationMeta.AddPointed) {
          cExpr = factory.app(factory.ref(ext.equationMeta.zro.getRef()), false, Collections.singletonList(cInstance));
        } else {
          ConcreteExpression one = factory.app(factory.ref(ext.equationMeta.ide.getRef()), false, Collections.singletonList(cInstance));
          cExpr = one;
          if (classDef == ext.equationMeta.Ring) {
            number = number.negate();
          }
          for (; number.compareTo(BigInteger.ONE) > 0; number = number.subtract(BigInteger.ONE)) {
            cExpr = factory.appBuilder(factory.ref(ext.equationMeta.plus.getRef())).app(cInstance, false).app(cExpr).app(one).build();
          }
          if (classDef == ext.equationMeta.Ring) {
            cExpr = factory.appBuilder(factory.ref(ext.equationMeta.negative.getRef())).app(cInstance, false).app(cExpr).build();
          }
        }
        return typechecker.typecheck(cExpr, expectedType);
      }
    }
    return typechecker.checkNumber(number, expectedType, contextData.getMarker());
  }
}
