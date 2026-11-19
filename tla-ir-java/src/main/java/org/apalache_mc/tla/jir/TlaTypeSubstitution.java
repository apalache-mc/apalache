package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.TlaType1;
import at.forsyte.apalache.tla.types.EqClass;
import at.forsyte.apalache.tla.types.Substitution;
import java.util.ArrayList;
import java.util.Map;
import java.util.Objects;
import scala.Tuple2;
import scala.jdk.javaapi.CollectionConverters;

/**
 * A reusable mapping from type-variable IDs to replacement TLA+ types.
 *
 * <p>Use {@code empty()} for an identity substitution or {@code of(...)} to supply
 * assignments. {@code applyOnce(...)} performs one simultaneous replacement, while
 * {@code applyFully(...)} also resolves replacement chains.</p>
 */
public final class TlaTypeSubstitution {
  private final Substitution scalaSubstitution;

  TlaTypeSubstitution(Substitution scalaSubstitution) {
    this.scalaSubstitution = scalaSubstitution;
  }

  Substitution scalaSubstitution() {
    return scalaSubstitution;
  }

  int maximumVariableId() {
    return CollectionConverters.asJava(scalaSubstitution.mapping()).entrySet().stream()
        .map(entry -> Math.max(
            CollectionConverters.asJava(entry.getKey().typeVars()).stream()
                .map(id -> ((Number) id).intValue())
                .reduce(-1, Math::max),
            TlaTypes.usedVariables(entry.getValue()).stream().reduce(-1, Math::max)))
        .reduce(-1, Math::max);
  }

  /** Returns a substitution that leaves every type unchanged. */
  public static TlaTypeSubstitution empty() {
    return new TlaTypeSubstitution(Substitution.empty());
  }

  /**
   * Creates a substitution from type-variable IDs to replacement types.
   *
   * @param assignments the assignments to copy
   * @return a reusable substitution independent of subsequent changes to the map
   * @throws IllegalArgumentException if an ID is negative
   */
  public static TlaTypeSubstitution of(Map<Integer, TlaType1> assignments) {
    var entries = new ArrayList<Tuple2<EqClass, TlaType1>>();
    Map.copyOf(assignments).forEach((id, type) -> {
      if (id < 0) throw new IllegalArgumentException("Type variable IDs must be nonnegative");
      entries.add(new Tuple2<>(EqClass.apply(id), type));
    });
    return new TlaTypeSubstitution(Substitution.apply(CollectionConverters.asScala(entries).toSeq()));
  }

  /**
   * Applies every matching assignment once without processing variables inside replacements.
   *
   * @param type the type to transform
   * @return the transformed type
   */
  public TlaType1 applyOnce(TlaType1 type) {
    return scalaSubstitution.sub(Objects.requireNonNull(type))._1();
  }

  /**
   * Repeatedly applies assignments until replacement chains are fully resolved.
   *
   * @param type the type to transform
   * @return the fully transformed type
   * @throws java.lang.IllegalStateException if assignments are cyclic or contain an invalid row replacement
   */
  public TlaType1 applyFully(TlaType1 type) {
    return scalaSubstitution.subRec(Objects.requireNonNull(type));
  }
}
