package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.TlaType1;
import at.forsyte.apalache.tla.types.TypeUnifier;
import at.forsyte.apalache.tla.types.TypeVarPool;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Stream;

/**
 * Finds substitutions that make two TLA+ types compatible.
 *
 * <p>A successful unification reports both the variable assignments and the resulting
 * common type. An ordinary type mismatch returns an empty {@code Optional}.</p>
 */
public final class TlaTypeUnifier {
  private final int maximumReservedVariableId;

  /**
   * Creates a unifier that avoids variable IDs used by the supplied types.
   *
   * <p>Pass the complete operator signature when only its result type will be unified.
   * With no arguments, only variables in the types being unified are reserved.</p>
   *
   * @param reservedTypes additional types whose variable IDs must not be reused
   */
  public TlaTypeUnifier(TlaType1... reservedTypes) {
    maximumReservedVariableId = Stream.of(reservedTypes)
        .flatMap(type -> TlaTypes.usedVariables(type).stream())
        .reduce(-1, Math::max);
  }

  /**
   * The result of successful type unification.
   *
   * @param substitution assignments that make the input types compatible
   * @param unifiedType the common type after applying those assignments
   */
  public record Unification(TlaTypeSubstitution substitution, TlaType1 unifiedType) {
    public Unification {
      Objects.requireNonNull(substitution);
      Objects.requireNonNull(unifiedType);
    }
  }

  /**
   * Attempts to unify two types, optionally honoring existing variable assignments.
   *
   * @param initial assignments to apply before solving, or empty to start without assignments
   * @param left the first type
   * @param right the second type
   * @return the successful unification, or empty if the types are incompatible
   * @throws java.lang.IllegalArgumentException if no fresh variable ID remains
   */
  public Optional<Unification> unify(
      Optional<TlaTypeSubstitution> initial, TlaType1 left, TlaType1 right) {
    var initialSubstitution = Objects.requireNonNull(initial).orElseGet(TlaTypeSubstitution::empty);
    var pool = freshVariablePool(
        initialSubstitution, Objects.requireNonNull(left), Objects.requireNonNull(right));
    var result = new TypeUnifier(pool).unify(initialSubstitution.scalaSubstitution(), left, right);
    if (pool.size() < 0) throw new IllegalArgumentException("No fresh type variable IDs remain");
    if (result.isEmpty()) return Optional.empty();

    var pair = result.get();
    return Optional.of(new Unification(new TlaTypeSubstitution(pair._1()), pair._2()));
  }

  private TypeVarPool freshVariablePool(
      TlaTypeSubstitution initial, TlaType1 left, TlaType1 right) {
    int maximum = Stream.of(left, right)
        .flatMap(type -> TlaTypes.usedVariables(type).stream())
        .reduce(Math.max(maximumReservedVariableId, initial.maximumVariableId()), Math::max);
    if (maximum == Integer.MAX_VALUE) {
      throw new IllegalArgumentException("No fresh type variable IDs remain");
    }
    return new TypeVarPool(maximum + 1);
  }
}
