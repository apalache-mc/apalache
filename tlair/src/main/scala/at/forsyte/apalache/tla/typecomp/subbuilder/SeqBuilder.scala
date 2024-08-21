package at.forsyte.apalache.tla.typecomp.subbuilder

import at.forsyte.apalache.tla.typecomp.BuilderUtil.{binaryFromUnsafe, ternaryFromUnsafe}
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.unsafe.UnsafeSeqBuilder

/**
 * Scope-safe builder for TlaSeqOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait SeqBuilder {
  private val unsafeBuilder = new UnsafeSeqBuilder {}

  /** {{{Append(seq,elem)}}} */
  def append(seq: TBuilderInstruction, elem: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(seq, elem)(unsafeBuilder.append)

  /** {{{leftSeq \o rightSeq}}} */
  def concat(leftSeq: TBuilderInstruction, rightSeq: TBuilderInstruction): TBuilderInstruction =
    binaryFromUnsafe(leftSeq, rightSeq)(unsafeBuilder.concat)

  /** {{{Head(seq)}}} */
  def head(seq: TBuilderInstruction): TBuilderInstruction = seq.map { unsafeBuilder.head }

  /** {{{Tail(seq)}}} */
  def tail(seq: TBuilderInstruction): TBuilderInstruction = seq.map { unsafeBuilder.tail }

  /** {{{Len(seq)}}} */
  def len(seq: TBuilderInstruction): TBuilderInstruction = seq.map { unsafeBuilder.len }

  /** {{{SubSeq(seq, fromIndex, toIndex)}}} */
  def subseq(
      seq: TBuilderInstruction,
      fromIndex: TBuilderInstruction,
      toIndex: TBuilderInstruction): TBuilderInstruction =
    ternaryFromUnsafe(seq, fromIndex, toIndex)(unsafeBuilder.subseq)

}
