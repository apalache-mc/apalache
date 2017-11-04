package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx}

import scala.collection.mutable

/**
  * Implements the rule SE-INT-CONST.
  *
  * @author Igor Konnov
  */
class IntConstRule(rewriter: SymbStateRewriter) extends RewritingRule {
  // cache the integer constants that are introduced for integer literals
  private val cache: mutable.Map[BigInt, String] = new mutable.HashMap()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaInt(_)) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaInt(n)) =>
        val intConst =
          if (cache.contains(n)) {
            cache(n)
          } else {
            // introduce a new constant
            val intConst = state.solverCtx.introIntConst()
            state.solverCtx.assertGroundExpr(OperEx(TlaOper.eq, NameEx(intConst), ValEx(TlaInt(n))))
            cache.put(n, intConst)
            intConst
          }
        val finalState =
          state.setTheory(IntTheory()).setRex(NameEx(intConst))
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("IntConstRule is not applicable")
    }
  }
}
