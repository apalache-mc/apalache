package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.{BoolT1, TlaType1}
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap, TypeComputationResult}

/**
 * Produces a SignatureMap for all control-flow operators
 *
 * @author
 *   Jure Kukovec
 */
object ControlOperSignatures {
  import at.forsyte.apalache.tla.lir.oper.TlaControlOper._
  import BuilderUtil._
  import FlexibleEquality._

  def getMap: SignatureMap = {

    // (Bool, t, t) => t
    val iteSig = signatureMapEntry(ifThenElse,
        { case Seq(BoolT1, t, tt) if compatible(t, tt) => commonSupertype(t, tt).get })

    def caseBodyT(seq: Seq[TlaType1]): Option[TypeComputationResult] = {
      val n = seq.size
      if (!(n >= 2 && n % 2 == 0))
        None
      else {
        val (cases, bodies) = seq.grouped(2).foldLeft((Seq.empty[TlaType1], Seq.empty[TlaType1])) {
          case ((lPartial, rPartial), Seq(cond, body)) =>
            (lPartial :+ cond, rPartial :+ body)
        }
        val t = bodies.head // n >= 2 => bodies.nonEmpty
        if (cases.forall(_ == BoolT1) && commonSeqSupertype(bodies).nonEmpty)
          commonSeqSupertype(bodies).map { Right(_) }
        else None
      }
    }

    // (Bool, t, ..., Bool, t) => t;
    val caseSig = signatureMapEntry(caseNoOther, Function.unlift(caseBodyT))

    def caseOtherBodyT(seq: Seq[TlaType1]): Option[TypeComputationResult] = {
      if (seq.isEmpty) None
      else {
        val otherT +: pairs = seq
        val withoutOther = caseBodyT(pairs)
        if (withoutOther.contains(Right(otherT))) withoutOther
        else None
      }

    }
    // (t, Bool, t, ..., Bool, t) => t;
    val caseOtherSig = signatureMapEntry(caseWithOther, Function.unlift(caseOtherBodyT))

    Map(
        iteSig,
        caseSig,
        caseOtherSig,
    )
  }
}
