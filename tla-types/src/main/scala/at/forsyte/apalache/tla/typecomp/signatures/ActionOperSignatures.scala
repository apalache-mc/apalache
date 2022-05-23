package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.typecomp.BuilderUtil
import at.forsyte.apalache.tla.typecomp.SignatureMap

/**
 * Produces a SignatureMap for all action operators
 *
 * @author
 *   Jure Kukovec
 */
object ActionOperSignatures {
  import TlaActionOper._
  import BuilderUtil._

  def getMap: SignatureMap = {

    // (t) => t
    val primeSig = signatureMapEntry(prime, { case Seq(t) => t })

    // (Bool, t) => Bool
    val stutterSigs = Seq(
        stutter,
        nostutter,
    ).map {
      signatureMapEntry(_, { case Seq(BoolT1, _) => BoolT1 })
    }

    // (Bool) => Bool
    val enabledSig = signatureMapEntry(enabled, { case Seq(BoolT1) => BoolT1 })

    // (t) => Bool
    val unchangedSig = signatureMapEntry(unchanged, { case Seq(_) => BoolT1 })

    // (Bool, Bool) => Bool
    val compSig = signatureMapEntry(composition, { case Seq(BoolT1, BoolT1) => BoolT1 })

    (stutterSigs :+ enabledSig :+ unchangedSig :+ primeSig :+ compSig).toMap
  }
}
