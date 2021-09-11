package org.arend.lib.pattern;

import org.arend.ext.core.body.CorePattern;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.variable.VariableRenamerFactory;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;
import java.util.List;
import java.util.Map;

public class ArendPattern implements CorePattern {
  private final CoreBinding binding;
  private final CoreDefinition definition;
  private final List<? extends CorePattern> subPatterns;
  private final CoreParameter parameters;
  private final VariableRenamerFactory renamer;

  public ArendPattern(CoreBinding binding, CoreDefinition definition, List<? extends CorePattern> subPatterns, CoreParameter parameters, VariableRenamerFactory renamer) {
    this.binding = binding;
    this.definition = definition;
    this.subPatterns = subPatterns;
    this.parameters = parameters;
    this.renamer = renamer;
  }

  @Override
  public @Nullable CoreBinding getBinding() {
    return binding;
  }

  @Override
  public String getBindingName() {
    CoreBinding binding = getBinding();
    return binding == null ? null : renamer.getNameFromBinding(binding, null);
  }

  @Override
  public @Nullable CoreDefinition getConstructor() {
    return definition;
  }

  @Override
  public @Nullable CoreParameter getParameters() {
    return parameters;
  }

  @Override
  public @NotNull List<? extends CorePattern> getSubPatterns() {
    return subPatterns == null ? Collections.emptyList() : subPatterns;
  }

  @Override
  public boolean isAbsurd() {
    return subPatterns == null;
  }

  @Override
  public @NotNull CoreParameter getAllBindings() {
    return parameters;
  }

  @Override
  public @NotNull CorePattern subst(@NotNull Map<? extends CoreBinding, ? extends CorePattern> map) {
    if (binding != null) {
      CorePattern pattern = map.get(binding);
      return pattern == null ? this : pattern;
    }

    return new ArendPattern(null, definition, PatternUtils.subst(subPatterns, map), parameters, renamer);
  }
}
