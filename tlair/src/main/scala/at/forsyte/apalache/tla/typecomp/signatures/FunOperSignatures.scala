package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.{FunT1, SetT1, TupT1}
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, PartialSignature, SignatureMap}

/**
 * Produces a SignatureMap for all function/record/tuple operators
 *
 * @author
 *   Jure Kukovec
 */
object FunOperSignatures {

  import TlaFunOper._
  import BuilderUtil._

  def getMap: SignatureMap = {

    // enum does NOT have a signature (the return type depends on the field value)

    // tuple does NOT have a signature, as it is overloaded for either tuples or explicit sequences.

    val funDefPartial: PartialSignature = {
      case t +: pairs if pairs.nonEmpty && pairs.size % 2 == 0 && pairs.grouped(2).forall {
            case Seq(tt, SetT1(tt2)) => tt == tt2
            case _                   => false
          } =>
        val ts = pairs.grouped(2).toSeq.map { case Seq(tt, _) => tt }
        if (ts.size == 1) FunT1(ts.head, t)
        else FunT1(TupT1(ts: _*), t)
    }
    // funDef is polyadic, with 2k + 1 args in general
    // (t1, t2, Set(t2), ..., tn, Set(tn) => <<t2, ..., tn>> -> t1 (or t2 -> t1)
    val funDefSig = signatureMapEntry(funDef, funDefPartial)

    // app, domain, and except are overloaded and don't have signatures

    Map(
        funDefSig
    )

  }

}
