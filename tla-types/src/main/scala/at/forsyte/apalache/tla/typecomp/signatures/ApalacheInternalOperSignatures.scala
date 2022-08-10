package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{ApalacheInternalOper, TlaBoolOper}
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap}

/**
 * Produces a SignatureMap for all internal Apalache operators
 *
 * @author
 *   Jure Kukovec
 */
object ApalacheInternalOperSignatures {
  import BuilderUtil._
  import ApalacheInternalOper._

  def getMap: SignatureMap = {

    // notSupportedByModelChecker has no signature, because we can't encode
    // (str) => t

    // (t,...,t) => Bool
    val distinctSig = signatureMapEntry(distinct, { case h +: tail if tail.forall(_ == h) => BoolT1 })

    // (Seq(t)) => Int
    val apalacheSeqCapacitySig = signatureMapEntry(apalacheSeqCapacity, { case Seq(_: SeqT1) => IntT1 })

    // (t, Set(t)) => Bool
    val selectInSetSig = signatureMapEntry(selectInSet, { case Seq(t, SetT1(tt)) if t == tt => BoolT1 })

    // (a, a -> b) => b
    val selectInFunSig = signatureMapEntry(selectInFun, { case Seq(aa, FunT1(a, b)) if a == aa => b })

    // storeInSet is separate, because it has variable arity.
    // (t, SetT1(t)) => Bool
    // or
    // (b, a -> b, a) => Bool
    val storeInSetSig =
      signatureMapEntry(
          storeInSet,
          {
            case Seq(t, SetT1(tt)) if t == tt                   => BoolT1
            case Seq(bb, FunT1(a, b), aa) if a == aa && b == bb => BoolT1
          },
      )

    // (t, Set(t)) => Bool
    val storeNotInSetSig = signatureMapEntry(storeNotInSet, { case Seq(t, SetT1(tt)) if t == tt => BoolT1 })

    // (a, a -> b) => Bool
    val storeNotInFunSig = signatureMapEntry(storeNotInFun, { case Seq(aa, FunT1(a, _)) if a == aa => BoolT1 })

    // (Set(t), Set(t)) => Set(t)
    val smtMapSig = Seq(
        TlaBoolOper.and,
        TlaBoolOper.or,
    ).map { op => signatureMapEntry(smtMap(op), { case Seq(SetT1(t), SetT1(tt)) if t == tt => SetT1(t) }) }.toMap

    // (Set(t)) => Bool
    val unconstrainArraySig = signatureMapEntry(unconstrainArray, { case Seq(_: SetT1) => BoolT1 })

    smtMapSig + distinctSig + apalacheSeqCapacitySig + selectInSetSig + selectInFunSig + storeInSetSig + storeNotInSetSig + storeNotInFunSig + unconstrainArraySig
  }
}
