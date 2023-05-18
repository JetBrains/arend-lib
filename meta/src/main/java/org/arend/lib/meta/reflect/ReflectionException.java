package org.arend.lib.meta.reflect;

import org.arend.ext.error.GeneralError;

public class ReflectionException extends RuntimeException {
  public final GeneralError error;

  public ReflectionException(GeneralError error) {
    this.error = error;
  }
}
