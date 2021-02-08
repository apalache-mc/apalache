package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.PowSetCtor
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.{BmcOper, TlaSetOper}

/**
 * This rule expands a powerset, that is, SUBSET S for a set S. In the future, it might also expand a set of functions,
 * that is, [S -> T], but this does not seem to be practical.
 *
 * @author Igor Konnov
 */
class SetExpandRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(BmcOper.expand, OperEx(TlaSetOper.SUBSET, _))    => true
      case OperEx(BmcOper.expand, OperEx(TlaSetOper.funSet, _, _)) => true
      case _                                                       => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(BmcOper.expand, OperEx(TlaSetOper.funSet, _, _)) =>
        throw new RewriterException("Trying to expand a set of functions. This will blow up the solver.", ex)

      case ex @ OperEx(BmcOper.expand, OperEx(TlaSetOper.SUBSET, basesetEx)) =>
        var nextState = rewriter.rewriteUntilDone(state.setRex(basesetEx))
        new PowSetCtor(rewriter).confringo(nextState, nextState.asCell)

      case e @ _ =>
        throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, e), state.ex)
    }
  }
}
