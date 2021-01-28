package at.forsyte.apalache.tla.bmcmt.rules.deprecated

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Implements the rule: SE-NE1.
  *
  * @author Igor Konnov
  */
@deprecated("It should be handled by Keramelizer")
class NeqRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaOper.ne, _, _) => true
      case _                        => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaOper.ne, left, right) =>
        val eqState =
          state.setRex(OperEx(TlaOper.eq, left, right))
        val nextState = rewriter.rewriteUntilDone(eqState)
        if (state.arena.cellFalse().toNameEx == nextState.ex) {
          nextState.setRex(state.arena.cellTrue().toNameEx)
        } else if (state.arena.cellTrue().toNameEx == nextState.ex) {
          nextState.setRex(state.arena.cellFalse().toNameEx)
        } else {
          val neState = nextState.setRex(OperEx(TlaBoolOper.not, nextState.ex))
          rewriter.rewriteUntilDone(neState)
        }

      case _ =>
        throw new RewriterException(
          "%s is not applicable".format(getClass.getSimpleName),
          state.ex
        )
    }
  }
}
