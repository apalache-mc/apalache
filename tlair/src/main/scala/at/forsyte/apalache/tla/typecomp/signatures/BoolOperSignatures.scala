package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{BoolT1, SetT1}
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap}

/**
 * Produces a SignatureMap for all Boolean operators
 *
 * @author
 *   Jure Kukovec
 */
object BoolOperSignatures {
  import TlaBoolOper._
  import BuilderUtil._

  /**
   * Returns a map that assigns a signature generator to each TlaBoolOper. Because some of the operators (quantifiers)
   * are polymorphic, their signatures will contain type variables produced on-demand by varPool.
   */
  def getMap: SignatureMap = {

    // And/or are polyadic, but all the args are Bool
    // (Bool, ..., Bool) => Bool
    val polyadic: SignatureMap = Seq(
        and,
        or,
    ).map { signatureMapEntry(_, { case seq if seq.forall(_ == BoolT1) => BoolT1 }) }.toMap

    // =>, <=> are binary, mono
    // (Bool, Bool) => Bool
    val binary: SignatureMap = Seq(
        implies,
        equiv,
    ).map { signatureMapEntry(_, { case Seq(BoolT1, BoolT1) => BoolT1 }) }.toMap

    // Quantifiers are polymorphic in the elemet/set types
    // (t, Set(t), Bool) => Bool
    val boundedQuant: SignatureMap = Seq(
        forall,
        exists,
    ).map { signatureMapEntry(_, { case Seq(t, SetT1(tt), BoolT1) if t == tt => BoolT1 }) }.toMap

    // (t, Bool) => Bool
    val unboundedQuant: SignatureMap = Seq(
        forallUnbounded,
        existsUnbounded,
    ).map { signatureMapEntry(_, { case Seq(_, BoolT1) => BoolT1 }) }.toMap

    // ~ is unary
    // (Bool) => Bool
    val notSig = signatureMapEntry(not, { case Seq(BoolT1) => BoolT1 })

    polyadic ++ binary ++ boundedQuant ++ unboundedQuant + notSig
  }

}
