package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

/**
  * Implements the rules: SE-AND{1,2,3,4,5}.
  */
class AndRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.rex match {
      case TlaRex(OperEx(TlaBoolOper.and, _*)) => true
      case _ => false
    }
  }

  override def apply(state: SymbState, dir: SymbStateRewriter.SearchDirection): SymbState = {
    def isTrue = Helper.isTrue(state.solverCtx)(_)
    def isFalse = Helper.isFalse(state.solverCtx)(_)
    state.rex match {
      case TlaRex(OperEx(TlaBoolOper.and, args@_*)) =>
        val (newState: SymbState, newRexes: Seq[Rex]) =
          rewriter.rewriteSeqUntilDone(state, args.map(e => TlaRex(e)))

        val noTrues = newRexes.filter(r => !isTrue(r))
        if (noTrues.isEmpty) {
          // empty conjunction is always true
          newState.setRex(PredRex(state.solverCtx.predTrue()))
        } else {
          if (noTrues.exists(isFalse)) {
            // one false constant makes the conjunction false
            newState.setRex(PredRex(state.solverCtx.predFalse()))
          } else {
            // the boring general case
            val newPred = newState.solverCtx.createPred()
            val smt2 = "(= %s (and %s))".format(newPred, noTrues.map(Helper.predRex_s))
            newState.solverCtx.assertSmt2(smt2)
            newState.setRex(PredRex(newPred))
          }
        }

      case _ =>
        throw new RewriterException("AndRule is not applicable")
    }
  }
}
