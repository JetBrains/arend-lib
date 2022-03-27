package org.arend.lib.error;

import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.error.quickFix.ErrorQuickFix;
import org.arend.ext.error.quickFix.RemoveErrorQuickFix;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class IgnoredArgumentError extends TypecheckingError {
  public IgnoredArgumentError(@NotNull ConcreteSourceNode cause) {
    super(Level.WARNING_UNUSED, "Argument is ignored", cause);
    withQuickFix(new RemoveErrorQuickFix("Remove argument"));
  }
}
