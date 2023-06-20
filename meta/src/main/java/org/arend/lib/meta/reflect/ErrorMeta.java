package org.arend.lib.meta.reflect;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.expr.CoreConCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.core.expr.CoreQNameExpression;
import org.arend.ext.core.expr.CoreStringExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.ext.prettyprinting.doc.LineDoc;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.lib.error.CustomTypecheckingError;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class ErrorMeta extends BaseMetaDefinition {
  @Dependency(module = "Reflect.Error") public CoreConstructor message;
  @Dependency(module = "Reflect.Error") public CoreConstructor hList;
  @Dependency(module = "Reflect.Error") public CoreConstructor text;
  @Dependency(module = "Reflect.Error") public CoreConstructor refDoc;
  @Dependency(module = "Reflect.Error") public CoreConstructor vList;
  @Dependency(module = "Reflect.Error") public CoreConstructor hang;
  @Dependency(module = "Reflect.Error") public CoreConstructor line;

  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { true };
  }

  @Override
  public boolean allowExcessiveArguments() {
    return false;
  }

  private LineDoc processLineDoc(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (!(expr instanceof CoreConCallExpression conCall)) return null;
    CoreConstructor con = conCall.getDefinition();
    if (con == hList) {
      List<LineDoc> list = TypecheckBuilder.processArray(conCall.getDefCallArguments().get(0), this::processLineDoc, null);
      if (list != null) {
        return hList(list);
      }
    } else if (con == text) {
      if (conCall.getDefCallArguments().get(0).normalize(NormalizationMode.WHNF) instanceof CoreStringExpression arg) {
        return text(arg.getString());
      }
    } else if (con == refDoc) {
      if (conCall.getDefCallArguments().get(0).normalize(NormalizationMode.WHNF) instanceof CoreQNameExpression arg) {
        return refDoc(arg.getRef());
      }
    }
    return null;
  }

  private Doc processDoc(CoreExpression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    if (!(expr instanceof CoreConCallExpression conCall)) return null;
    CoreConstructor con = conCall.getDefinition();
    if (con == vList) {
      List<Doc> list = TypecheckBuilder.processArray(conCall.getDefCallArguments().get(0), this::processDoc, null);
      if (list != null) {
        return vList(list);
      }
    } else if (con == hang) {
      Doc doc1 = processDoc(conCall.getDefCallArguments().get(0));
      Doc doc2 = processDoc(conCall.getDefCallArguments().get(1));
      if (doc1 != null && doc2 != null) {
        return hang(doc1, doc2);
      }
    } else if (con == line) {
      return processLineDoc(conCall.getDefCallArguments().get(0));
    }
    return null;
  }

  private TypecheckingError processError(CoreExpression expr, ConcreteExpression marker) {
    if (expr instanceof CoreConCallExpression conCall && conCall.getDefinition() == message) {
      LineDoc doc1 = processLineDoc(conCall.getDefCallArguments().get(0));
      Doc doc2 = processDoc(conCall.getDefCallArguments().get(1));
      if (doc1 != null && doc2 != null) {
        return new CustomTypecheckingError(doc1, doc2, marker);
      }
    }
    return null;
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    TypedExpression arg = typechecker.typecheck(contextData.getArguments().get(0).getExpression(), null);
    if (arg == null) return null;
    CoreExpression expr = arg.getExpression().normalize(NormalizationMode.WHNF);
    if (expr instanceof CoreStringExpression) {
      typechecker.getErrorReporter().report(new TypecheckingError(((CoreStringExpression) expr).getString(), contextData.getMarker()));
    } else {
      TypecheckingError error = processError(expr, contextData.getMarker());
      typechecker.getErrorReporter().report(error != null ? error : new TypecheckingError("Invalid expression. Expected either a string or an expression of type 'Reflect.IO.Error'", contextData.getArguments().get(0).getExpression()));
    }
    return null;
  }
}
