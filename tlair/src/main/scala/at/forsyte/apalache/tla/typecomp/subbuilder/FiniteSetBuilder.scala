package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeFiniteSetBuilder

/**
 * Scope-safe builder for TlaFiniteSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait FiniteSetBuilder {
  private val unsafeBuilder = new UnsafeFiniteSetBuilder {}

  /** {{{IsFiniteSet(set)}}} */
  def isFiniteSet(set: TBuilderInstruction): TBuilderInstruction = set.map(unsafeBuilder.isFiniteSet)

  /** {{{Cardinality(set)}}} */
  def cardinality(set: TBuilderInstruction): TBuilderInstruction = set.map(unsafeBuilder.cardinality)
}
