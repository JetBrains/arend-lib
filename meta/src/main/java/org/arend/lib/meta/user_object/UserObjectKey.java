package org.arend.lib.meta.user_object;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.userData.Key;

import java.util.List;
import java.util.Objects;

public class UserObjectKey extends Key<List<ConcreteExpression>> {
  private final ArendRef myReference;

  public UserObjectKey(ArendRef reference) {
    super("user_object");
    myReference = reference;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    UserObjectKey that = (UserObjectKey) o;
    return Objects.equals(myReference, that.myReference);
  }

  @Override
  public int hashCode() {
    return Objects.hash(myReference);
  }
}
