package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeFiniteSetBuilder

/**
 * Scope-safe builder for TlaFiniteSetOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait FiniteSetBuilder extends UnsafeFiniteSetBuilder {

  /** IsFiniteSet(set) */
  def isFiniteSet(set: TBuilderInstruction): TBuilderInstruction = set.map(_isFiniteSet)

  /** Cardinality(set) */
  def cardinality(set: TBuilderInstruction): TBuilderInstruction = set.map(_cardinality)
}
