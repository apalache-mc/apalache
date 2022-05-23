package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, SetT1, TlaType1}
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, PartialSignature, SignatureMap}

/**
 * Produces a SignatureMap for all arithmetic operators
 *
 * @author
 *   Jure Kukovec
 */
object ArithOperSignatures {
  import TlaArithOper._
  import BuilderUtil._

  /** Returns a map that assigns a signature generator to each TLaArithOper. */
  def getMap: SignatureMap = {

    def binaryPartial(retT: TlaType1): PartialSignature = { case Seq(IntT1, IntT1) =>
      retT
    }

    // All these operators have fixed arity 2 and none of them are polymorphic.
    // Signature generators for these operators ignore the arity hint.
    // (Int, Int) => Int
    val intOpers: SignatureMap = Seq(
        plus,
        minus,
        mult,
        div,
        mod,
        exp,
    ).map { signatureMapEntry(_, binaryPartial(IntT1)) }.toMap

    // Same as above, except they return BoolT1 instead of IntT1
    // (Int, Int) => Bool
    val boolOpers: SignatureMap = Seq(
        lt,
        gt,
        le,
        ge,
    ).map { signatureMapEntry(_, binaryPartial(BoolT1)) }.toMap

    // - is unary and dotdot returns a set
    // (Int) => Int,
    // (Int,Int) => Set(Int)
    val rest: SignatureMap = Map(
        signatureMapEntry(uminus, { case Seq(IntT1) => IntT1 }),
        signatureMapEntry(dotdot, binaryPartial(SetT1(IntT1))),
    )
    intOpers ++ boolOpers ++ rest
  }

}
