package org.arend.lib.meta.reflect;

import org.arend.ext.error.GeneralError;

public class TypecheckException extends RuntimeException {
  public final GeneralError error;

  public TypecheckException(GeneralError error) {
    this.error = error;
  }
}
