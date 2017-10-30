package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

/**
  * Implements the rules: SE-OR{1,2,3,4,5}.
  *
  * Note that this rule does not implement case split as prescribed by rule SE-SEARCH-SPLIT.
  */
class OrRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.rex match {
      case TlaRex(OperEx(TlaBoolOper.or, _*)) => true
      case _ => false
    }
  }

  override def apply(state: SymbState, dir: SymbStateRewriter.SearchDirection): SymbState = {
    def isTrue = Helper.isTrue(state.solverCtx)(_)
    def isFalse = Helper.isFalse(state.solverCtx)(_)
    state.rex match {
      case TlaRex(OperEx(TlaBoolOper.or, args@_*)) =>
        val (newState: SymbState, newRexes: Seq[Rex]) =
          rewriter.rewriteSeqUntilDone(state, args.map(e => TlaRex(e)))

        val noFalses = newRexes.filter(r => !isFalse(r))
        if (noFalses.isEmpty) {
          // empty disjunction is always false
          newState.setRex(PredRex(state.solverCtx.predFalse()))
        } else {
          if (noFalses.exists(isTrue)) {
            // one true constant makes the disjunction true
            newState.setRex(PredRex(state.solverCtx.predTrue()))
          } else {
            // the boring general case
            val newPred = newState.solverCtx.createPred()
            val smt2 = "(= %s (or %s))".format(newPred, noFalses.map(Helper.predRex_s))
            newState.solverCtx.assertSmt2(smt2)
            newState.setRex(PredRex(newPred))
          }
        }

      case _ =>
        throw new RewriterException("OrRule is not applicable")
    }
  }
}
