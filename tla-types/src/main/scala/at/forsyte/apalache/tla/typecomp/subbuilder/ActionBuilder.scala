package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeActionBuilder
import at.forsyte.apalache.tla.typecomp.BuilderUtil.binaryFromUnsafe

/**
 * Type-safe builder for TlaActionOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait ActionBuilder extends UnsafeActionBuilder {

  /** e' */
  def prime(e: TBuilderInstruction): TBuilderInstruction = e.map(_prime)

  /** [A]_e */
  def stutt(A: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(A, e)(_stutt)

  /** <A>_e */
  def nostutt(A: TBuilderInstruction, e: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(A, e)(_nostutt)

  /** ENABLED A */
  def enabled(A: TBuilderInstruction): TBuilderInstruction = A.map(_enabled)

  /** UNCHANGED e */
  def unchanged(e: TBuilderInstruction): TBuilderInstruction = e.map(_unchanged)

  /** A \cdot B */
  def comp(A: TBuilderInstruction, B: TBuilderInstruction): TBuilderInstruction = binaryFromUnsafe(A, B)(_comp)
}
