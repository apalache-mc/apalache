package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{BoolT1, OperEx, TlaEx}

/**
 * Implements logical negation.
 *
 * @author
 *   Igor Konnov
 */
class NegRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.not, _) => true
      case _                          => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaBoolOper.not, ex: TlaEx) =>
        var newState = rewriter.rewriteUntilDone(state.setRex(ex))
        newState = newState.updateArena(_.appendCell(BoolT1))
        val pred = newState.arena.topCell
        rewriter.solverContext.assertGroundExpr(tla.eql(tla.not(pred.toNameEx), newState.ex))
        newState.setRex(pred.toNameEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
