package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap}

/**
 * Produces a SignatureMap for all internal Apalache operators
 *
 * @author
 *   Jure Kukovec
 */
object ApalacheOperSignatures {
  import ApalacheOper._
  import BuilderUtil._
  import FlexibleEquality._

  def getMap: SignatureMap = {

    // (t,t) => Bool
    val assignSig = signatureMapEntry(assign, { case Seq(t, tt) if compatible(t, tt) => BoolT1 })

    // gen has no signature, because we can't encode
    // (Int) => t

    // (Bool) => Bool
    val skolemSig = signatureMapEntry(skolem, { case Seq(BoolT1) => BoolT1 })

    // (Set(t)) => t
    val guessSig = signatureMapEntry(guess, { case Seq(SetT1(t)) => t })

    // (Set(Set(t))) => Set(Set(t))
    // or
    // (Set(a -> b)) => Set(a -> b)
    val expandSig = signatureMapEntry(expand,
        {
          case Seq(powsetT @ SetT1(_: SetT1)) => powsetT
          case Seq(funsetT @ SetT1(_: FunT1)) => funsetT
        })

    // (Bool) => Bool
    val constCardSig = signatureMapEntry(constCard, { case Seq(BoolT1) => BoolT1 })

    // funAsSeq should not be constructed

    // (Int, Int => t) => Seq(t)
    val mkSeqSig = signatureMapEntry(mkSeq, { case Seq(IntT1, OperT1(Seq(IntT1), t)) => SeqT1(t) })

    // ((t, Int) => t, Int, t) => t
    val repeatSig = signatureMapEntry(repeat, {
      case Seq(OperT1(Seq(IntT1, t), t1), IntT1, t2) if compatible(t, t1)  && compatible(t, t2) => t
    })

    // ((a,b) => a, a, Set(b)) => a
    val foldSetSig = signatureMapEntry(foldSet,
        {
          case Seq(OperT1(Seq(a, b), a1), a2, SetT1(b1))
              if commonSeqSupertype(Seq(a, a1, a2)).nonEmpty && compatible(b, b1) =>
            commonSeqSupertype(Seq(a, a1, a2)).get
        })

    // ((a,b) => a, a, Seq(b)) => a
    val foldSeqSig = signatureMapEntry(foldSeq,
        {
          case Seq(OperT1(Seq(a, b), a1), a2, SeqT1(b1))
              if commonSeqSupertype(Seq(a, a1, a2)).nonEmpty && compatible(b, b1) =>
            commonSeqSupertype(Seq(a, a1, a2)).get
        })

    // (Set(<<a,b>>)) => a -> b
    val setAsFunSig = signatureMapEntry(setAsFun, { case Seq(SetT1(TupT1(a, b))) => FunT1(a, b) })

    Map(
        assignSig,
        skolemSig,
        guessSig,
        expandSig,
        constCardSig,
        mkSeqSig,
        repeatSig,
        foldSetSig,
        foldSeqSig,
        setAsFunSig,
    )
  }
}
