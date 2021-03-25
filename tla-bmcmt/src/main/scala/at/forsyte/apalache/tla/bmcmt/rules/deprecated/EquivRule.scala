package at.forsyte.apalache.tla.bmcmt.rules.deprecated

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.rules.SubstRule
import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
 * Implements an equivalence A <=> B by rewriting it to A = B.
 *
 * @author Igor Konnov
 */
@deprecated("Normalizer takes care of it")
class EquivRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val substRule = new SubstRule(rewriter)
  private val simplifier = new ConstSimplifierForSmt()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.equiv, _, _) => true
      case _                               => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaBoolOper.equiv, left, right) =>
        var leftState = rewriter.rewriteUntilDone(state.setRex(left))
        val rightState = rewriter.rewriteUntilDone(leftState.setRex(right))
        var nextState = rightState.updateArena(_.appendCell(BoolT()))
        val pred = nextState.arena.topCell
        val eq: TlaEx = tla.eql(pred.toNameEx, tla.equiv(leftState.ex, rightState.ex))
        rewriter.solverContext.assertGroundExpr(eq)
        nextState.setRex(pred.toNameEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
