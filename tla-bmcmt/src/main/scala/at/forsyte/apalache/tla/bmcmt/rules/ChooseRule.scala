package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper


/**
  * Implements the rules: SE-LOG-CHO1.
  * Similar to TLC, we implement a non-deterministic choice.
  * It is not hard to add the requirement of determinism, but that will
  * probably affect efficiency.
  *
  * TODO: add determinism as an option.
  *
  * @author Igor Konnov
  */
class ChooseRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickRule = new PickFromAndFunMerge(rewriter)

  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(TlaOper.chooseBounded, _, _, _) =>
        true

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaOper.chooseBounded, varName, set, pred) =>
        // compute set comprehension and then pick an element from it
        val filterEx = tla.filter(varName, set, pred)
        val filterState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(filterEx))
        // pick an arbitrary witness
        val setCell = filterState.arena.findCellByNameEx(filterState.ex)
        rewriter.coerce(pickRule.pick(setCell, filterState), state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
