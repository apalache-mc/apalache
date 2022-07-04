package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.oper.TlaTempOper
import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap}

/**
 * Produces a SignatureMap for all temporal operators
 *
 * @author
 *   Jure Kukovec
 */
object TemporalOperSignatures {
  import BuilderUtil._
  import TlaTempOper._

  def getMap: SignatureMap = {

    // (Bool) => Bool
    val unary: SignatureMap = Seq(
        box,
        diamond,
    ).map { signatureMapEntry(_, { case Seq(BoolT1) => BoolT1 }) }.toMap

    // (Bool, Bool) => Bool
    val binaryBool: SignatureMap = Seq(
        leadsTo,
        guarantees,
    ).map { signatureMapEntry(_, { case Seq(BoolT1, BoolT1) => BoolT1 }) }.toMap

    // (t, Bool) => Bool
    val binaryAnyBool: SignatureMap = Seq(
        weakFairness,
        strongFairness,
        EE,
        AA,
    ).map { signatureMapEntry(_, { case Seq(_, BoolT1) => BoolT1 }) }.toMap

    unary ++ binaryBool ++ binaryAnyBool
  }

}
