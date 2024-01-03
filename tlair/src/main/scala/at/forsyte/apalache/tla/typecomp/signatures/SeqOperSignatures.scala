package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSeqOper
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap}

/**
 * Produces a SignatureMap for all sequence operators
 *
 * @author
 *   Jure Kukovec
 */
object SeqOperSignatures {
  import TlaSeqOper._
  import BuilderUtil._
  import FlexibleEquality._

  /** Returns a map that assigns a signature generator to each TLaArithOper. */
  def getMap: SignatureMap = {

    // (Seq(t)) => t
    val headSig = signatureMapEntry(head, { case Seq(SeqT1(t)) => t })

    // (Seq(t)) => Seq(t)
    val tailSig = signatureMapEntry(tail, { case Seq(st: SeqT1) => st })

    // (Seq(t), t) => Seq(t)
    val appendSig = signatureMapEntry(append,
        { case Seq(SeqT1(t), tt) if compatible(t, tt) => commonSupertype(t, tt).map(SeqT1).get })

    // (Seq(t), Seq(t)) => Seq(t)
    val concatSig = signatureMapEntry(concat,
        { case Seq(SeqT1(t), SeqT1(tt)) if compatible(t, tt) => commonSupertype(t, tt).map(SeqT1).get })

    // (Seq(t)) => Int
    val lenSig = signatureMapEntry(len, { case Seq(_: SeqT1) => IntT1 })

    // (Seq(t), Int, Int) => Seq(t)
    val subseqSig = signatureMapEntry(subseq, { case Seq(st: SeqT1, IntT1, IntT1) => st })

    // (Seq(t), (Seq(t)) => Bool) => Seq(t)
    // selectseq is rewired in __rewire_sequences_in_apalache.tla and should not be created

    Map(
        headSig,
        tailSig,
        appendSig,
        concatSig,
        lenSig,
        subseqSig,
    )
  }
}
