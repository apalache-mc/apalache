package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import at.forsyte.apalache.tla.typecomp.SignatureGenMap

/**
 * Produces a SignatureMap for all base operators
 *
 * @author
 *   Jure Kukovec
 */
object BaseOperSignatures {
  import TlaOper._

  def getMap(varPool: TypeVarPool): SignatureGenMap = {

    // (t, t) => Bool
    val cmpSigs: SignatureGenMap = Seq(
        TlaOper.eq,
        TlaOper.ne,
    ).map {
      _ -> { _: Int =>
        val t = varPool.fresh
        OperT1(Seq(t, t), BoolT1())
      }
    }.toMap

    //  ( (t1, ..., tn) => t, t1, ..., tn ) => t
    val applySig = TlaOper.apply -> { n: Int =>
      val t +: ts = varPool.fresh(n)
      OperT1(OperT1(ts, t) +: ts, t)
    }

    // (t, Set(t), Bool) => t
    val chooseBoundedSig = chooseBounded -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(t, SetT1(t), BoolT1()), t)
    }

    // (t, Bool) => t
    val chooseUnboundedSig = chooseUnbounded -> { _: Int =>
      val t = varPool.fresh
      OperT1(Seq(t, BoolT1()), t)
    }

    // (t, t1, ..., tn) => t
    val labelSig = label -> { n: Int =>
      val all @ t +: _ = varPool.fresh(n)
      OperT1(all, t)

    }

    cmpSigs + applySig + chooseBoundedSig + chooseUnboundedSig + labelSig

  }
}
