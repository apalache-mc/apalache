package at.forsyte.apalache.tla.typecmp.signatures

import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{BoolT1, OperT1, SetT1}
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import at.forsyte.apalache.tla.typecmp.{liftOper, SignatureMap}

/**
 * Produces a SignatureMap for all Boolean operators
 *
 * @author
 *   Jure Kukovec
 */
object BoolOperSignatures {
  import TlaBoolOper._

  def getMap(varPool: TypeVarPool): SignatureMap = {

    // And/or are polyadic, but all the args are Bool
    // (Bool, ..., Bool) => Bool
    val polyadic: SignatureMap = Seq(
        and,
        or,
    ).map {
      _ -> { n: Int =>
        OperT1(Seq.fill(n)(BoolT1()), BoolT1())
      }
    }.toMap

    // =>, <=> are binary, mono
    // (Bool, Bool) => Bool
    val binary: SignatureMap = Seq(
        implies,
        equiv,
    ).map { _ -> liftOper(OperT1(Seq.fill(2)(BoolT1()), BoolT1())) }.toMap

    // Quantifiers are polymorphic in the elemet/set types
    // (t, Set(t), Bool) => Bool
    val boundedQuant: SignatureMap = Seq(
        forall,
        exists,
    ).map {
      _ -> { _: Int =>
        val t = varPool.fresh
        val setT = SetT1(t)
        OperT1(Seq(t, setT, BoolT1()), BoolT1())
      }
    }.toMap

    // (t, Bool) => Bool
    val unboundedQuant: SignatureMap = Seq(
        forallUnbounded,
        existsUnbounded,
    ).map {
      _ -> { _: Int =>
        val t = varPool.fresh
        OperT1(Seq(t, BoolT1()), BoolT1())
      }
    }.toMap

    // ~ is unary
    // (Bool) => Bool
    val notSig: (TlaBoolOper, Int => OperT1) = not -> OperT1(Seq(BoolT1()), BoolT1())

    polyadic ++ binary ++ boundedQuant ++ unboundedQuant + notSig
  }

}
