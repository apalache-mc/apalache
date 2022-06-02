package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.{FunT1, SetT1}
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.typecomp.{BuilderUtil, SignatureMap}

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

    // We only need the ternary signature, because the builder interface constructs
    // [x1 \in S1, ..., xn \in Sn |-> e] as [<<x1, ..., xn>> \in S1 \X .. \X Sn |-> e]
    // (t1, t2, Set(t2)) => t2 -> t1
    val funDefSig = signatureMapEntry(funDef, { case Seq(t1, t2, SetT1(tt)) if t2 == tt => FunT1(t2, t1) })

    // app, domain, and except are overloaded and don't have signatures

    Map(
        funDefSig
    )

  }

}
