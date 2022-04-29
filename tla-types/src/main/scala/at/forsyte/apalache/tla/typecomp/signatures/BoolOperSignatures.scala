package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{BoolT1, OperT1, SetT1}
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import at.forsyte.apalache.tla.typecomp.{liftOper, SignatureGenMap}

/**
 * Produces a SignatureMap for all Boolean operators
 *
 * @author
 *   Jure Kukovec
 */
object BoolOperSignatures {
  import TlaBoolOper._

  /**
   * Returns a map that assigns a signature generator to each TlaBoolOper. Because some of the operators (quantifiers)
   * are polymorphic, their signatures will contain type variables produced on-demand by varPool.
   */
  def getMap(varPool: TypeVarPool): SignatureGenMap = {

    // And/or are polyadic, but all the args are Bool
    // (Bool, ..., Bool) => Bool
    val polyadic: SignatureGenMap = Seq(
        and,
        or,
    ).map {
      _ -> { n: Int =>
        OperT1(Seq.fill(n)(BoolT1()), BoolT1())
      }
    }.toMap

    // =>, <=> are binary, mono
    // (Bool, Bool) => Bool
    val binary: SignatureGenMap = Seq(
        implies,
        equiv,
    ).map { _ -> liftOper(OperT1(Seq.fill(2)(BoolT1()), BoolT1())) }.toMap

    // Quantifiers are polymorphic in the elemet/set types
    // (t, Set(t), Bool) => Bool
    val boundedQuant: SignatureGenMap = Seq(
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
    val unboundedQuant: SignatureGenMap = Seq(
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
