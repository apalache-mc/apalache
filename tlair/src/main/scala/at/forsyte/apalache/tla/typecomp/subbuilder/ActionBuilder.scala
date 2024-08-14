package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeActionBuilder
import at.forsyte.apalache.tla.typecomp.BuilderUtil.binaryFromUnsafe

/**
 * Scope-safe builder for TlaActionOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ActionBuilder {
  private val unsafeBuilder = new UnsafeActionBuilder {}

  /** {{{e'}}} */
  def prime(e: TBuilderInstruction): TBuilderInstruction = e.map(unsafeBuilder.prime)

  /** {{{[A]_e}}} */
  def stutt(A: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(A, e)(unsafeBuilder.stutt)

  /** {{{<A>_e}}} */
  def nostutt(A: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(A, e)(unsafeBuilder.nostutt)

  /** {{{ENABLED A}}} */
  def enabled(A: TBuilderInstruction): TBuilderInstruction = A.map(unsafeBuilder.enabled)

  /** {{{UNCHANGED e}}} */
  def unchanged(e: TBuilderInstruction): TBuilderInstruction = e.map(unsafeBuilder.unchanged)

  /** {{{A \cdot B}}} */
  def comp(A: TBuilderInstruction, B: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(A, B)(unsafeBuilder.comp)
}
