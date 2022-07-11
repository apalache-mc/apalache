package at.forsyte.apalache.tla.typecomp.unsafe

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.oper.TlaSeqOper

/**
 * Scope-unsafe builder for TlaSeqOper expressions.
 *
 * @author
 *   Jure Kukovec
 */
class UnsafeSeqBuilder extends ProtoBuilder {

  /** {{{Append(seq,elem)}}} */
  def append(seq: TlaEx, elem: TlaEx): TlaEx = buildBySignatureLookup(TlaSeqOper.append, seq, elem)

  /** {{{leftSeq \o rightSeq}}} */
  def concat(leftSeq: TlaEx, rightSeq: TlaEx): TlaEx = buildBySignatureLookup(TlaSeqOper.concat, leftSeq, rightSeq)

  /** {{{Head(seq)}}} */
  def head(seq: TlaEx): TlaEx = buildBySignatureLookup(TlaSeqOper.head, seq)

  /** {{{Tail(seq)}}} */
  def tail(seq: TlaEx): TlaEx = buildBySignatureLookup(TlaSeqOper.tail, seq)

  /** {{{Len(seq)}}} */
  def len(seq: TlaEx): TlaEx = buildBySignatureLookup(TlaSeqOper.len, seq)

  /** {{{SubSeq(seq, fromIndex, toIndex)}}} */
  def subseq(seq: TlaEx, fromIndex: TlaEx, toIndex: TlaEx): TlaEx =
    buildBySignatureLookup(TlaSeqOper.subseq, seq, fromIndex, toIndex)

}
