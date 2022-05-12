package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSeqOper
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import at.forsyte.apalache.tla.typecomp.SignatureGenMap

/**
 * Produces a SignatureMap for all sequence operators
 *
 * @author
 *   Jure Kukovec
 */
object SeqOperSignatures {
  import TlaSeqOper._

  /** Returns a map that assigns a signature generator to each TLaArithOper. */
  def getMap(varPool: TypeVarPool): SignatureGenMap = {

    // (Seq(t)) => t
    val headSig = head -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SeqT1(t)), t)
    }

    // (Seq(t)) => Seq(t)
    val tailSig = tail -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SeqT1(t)), SeqT1(t))
    }

    // (Seq(t), t) => Seq(t)
    val appendSig = append -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SeqT1(t), t), SeqT1(t))
    }

    // (Seq(t), Seq(t)) => Seq(t)
    val concatSig = concat -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SeqT1(t), SeqT1(t)), SeqT1(t))
    }

    // (Seq(t)) => Int
    val lenSig = len -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SeqT1(t)), IntT1())
    }

    // (Seq(t), Int, Int) => Seq(t)
    val subseqSig = subseq -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(SeqT1(t), IntT1(), IntT1()), SeqT1(t))
    }

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
