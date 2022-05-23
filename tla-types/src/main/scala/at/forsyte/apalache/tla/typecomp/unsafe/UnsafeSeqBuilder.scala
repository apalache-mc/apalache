package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaSeqOper

/**
 * Type-unsafe builder for TlaSeqOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
trait UnsafeSeqBuilder extends ProtoBuilder {

  /** Append(seq,elem) */
  protected def _append(seq: TlaEx, elem: TlaEx): TlaEx = buildBySignatureLookup(TlaSeqOper.append, seq, elem)

  /** leftSeq \o rightSeq */
  protected def _concat(leftSeq: TlaEx, rightSeq: TlaEx): TlaEx =
    buildBySignatureLookup(TlaSeqOper.concat, leftSeq, rightSeq)

  /** Head(seq) */
  protected def _head(seq: TlaEx): TlaEx = buildBySignatureLookup(TlaSeqOper.head, seq)

  /** Tail(seq) */
  protected def _tail(seq: TlaEx): TlaEx = buildBySignatureLookup(TlaSeqOper.tail, seq)

  /** Len(seq) */
  protected def _len(seq: TlaEx): TlaEx = buildBySignatureLookup(TlaSeqOper.len, seq)

  /** SubSeq(seq, fromIndex, toIndex) */
  protected def _subseq(seq: TlaEx, fromIndex: TlaEx, toIndex: TlaEx): TlaEx =
    buildBySignatureLookup(TlaSeqOper.subseq, seq, fromIndex, toIndex)

}
