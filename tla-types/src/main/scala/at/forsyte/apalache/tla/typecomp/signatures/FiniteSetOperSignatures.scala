package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.oper.TlaFiniteSetOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap}

/**
 * Produces a SignatureMap for all finite set operators
 *
 * @author
 *   Jure Kukovec
 */
object FiniteSetOperSignatures {
  import BuilderUtil._
  import TlaFiniteSetOper._

  def getMap: SignatureMap = {

    // (Set(t)) => Bool
    val isFiniteSetSig = signatureMapEntry(isFiniteSet, { case Seq(SetT1(_)) => BoolT1 })

    // (Set(t)) => Int
    val cardinalitySig = signatureMapEntry(cardinality, { case Seq(SetT1(_)) => IntT1 })

    Map(isFiniteSetSig, cardinalitySig)
  }
}
