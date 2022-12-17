package org.arend.lib;

import org.arend.ext.LiteralTypechecker;
import org.arend.ext.concrete.ConcreteAppBuilder;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.expr.CoreDataCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreFieldCallExpression;
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

  private ConcreteExpression applyInstance(ConcreteExpression instance, ConcreteExpression expr, ConcreteFactory factory) {
    return instance == null ? expr : factory.app(expr, false, Collections.singletonList(instance));
  }

  @Override
  public @Nullable TypedExpression typecheckNumber(@NotNull BigInteger number, @NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    CoreExpression expectedType = contextData.getExpectedType() == null ? null : contextData.getExpectedType().normalize(NormalizationMode.WHNF);
    if (expectedType != null && !(expectedType instanceof CoreDataCallExpression && (((CoreDataCallExpression) expectedType).getDefinition() == ext.prelude.getNat() || ((CoreDataCallExpression) expectedType).getDefinition() == ext.prelude.getInt()))) {
      boolean generate;
      TypedExpression instance;
      if (expectedType instanceof CoreFieldCallExpression && ((CoreFieldCallExpression) expectedType).getDefinition() == ext.carrier) {
        instance = null;
        generate = true;
      } else {
        CoreClassDefinition classDef = number.equals(BigInteger.ZERO) ? ext.AddPointed : number.equals(BigInteger.ONE) ? ext.Pointed : number.signum() == -1 ? ext.equationMeta.Ring : ext.equationMeta.Semiring;
        instance = classDef == null ? null : Utils.findInstance(new SubclassSearchParameters(classDef), ext.carrier, expectedType, typechecker, contextData.getMarker());
        generate = instance != null;
      }
      if (generate) {
        ConcreteFactory factory = ext.factory.withData(contextData.getMarker());
        ConcreteExpression cExpr;
        ConcreteExpression cInstance = instance == null ? null : factory.core(null, instance);
        if (number.equals(BigInteger.ZERO) || number.equals(BigInteger.ONE) || number.equals(BigInteger.ONE.negate())) {
          cExpr = number.equals(BigInteger.ZERO) ? applyInstance(cInstance, factory.ref(ext.zro.getRef()), factory) : number.equals(BigInteger.ONE) ? applyInstance(cInstance, factory.ref(ext.ide.getRef()), factory) : factory.app(applyInstance(cInstance, factory.ref(ext.equationMeta.negative.getRef()), factory), true, factory.ref(ext.ide.getRef()));
        } else {
          ConcreteAppBuilder builder = factory.appBuilder(factory.ref((number.signum() == -1 ? ext.equationMeta.intCoef : ext.equationMeta.natCoef).getRef()));
          if (cInstance != null) {
            builder.app(cInstance, false);
          }
          cExpr = builder.app(factory.number(number)).build();
        }
        return typechecker.typecheck(cExpr, expectedType);
      }
    }
    return typechecker.checkNumber(number, expectedType, contextData.getMarker());
  }
}
