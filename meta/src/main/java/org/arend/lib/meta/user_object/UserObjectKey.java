package org.arend.lib.meta.user_object;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.userData.Key;

import java.util.List;
import java.util.Objects;

public class UserObjectKey extends Key<List<ConcreteExpression>> {
  private final String myName;

  public UserObjectKey(String name) {
    super("user_object:" + name);
    myName = name;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    UserObjectKey that = (UserObjectKey) o;
    return Objects.equals(myName, that.myName);
  }

  @Override
  public int hashCode() {
    return Objects.hash(myName);
  }
}
