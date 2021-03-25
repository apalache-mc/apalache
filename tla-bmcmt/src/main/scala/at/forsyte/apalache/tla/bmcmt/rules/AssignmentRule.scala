package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
 * Implements the assignment rule.
 * Similar to TLC, this is a special form of x' \in S operator that is treated
 * as an assignment of a value from S to the variable x'.
 *
 * Since version 0.6.x, most of the work is delegated to existential quantification, that is,
 * assignments are treated as \E t \in S: x' = t
 *
 * @author Igor Konnov
 */
class AssignmentRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickRule = new CherryPick(rewriter)

  override def isApplicable(state: SymbState): Boolean = {
    def isUnbound(name: String) =
      (!ArenaCell.isValidName(name)
        && !state.binding.contains(name + "'"))

    state.ex match {
      case OperEx(ApalacheOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), _) =>
        isUnbound(name)

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      // general case
      case OperEx(ApalacheOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), rhs) =>
        val nextState = rewriter.rewriteUntilDone(state.setRex(rhs))
        val rhsCell = nextState.arena.findCellByNameEx(nextState.ex)
        nextState
          .setRex(state.arena.cellTrue().toNameEx) // just return TRUE
          .setBinding(Binding(nextState.binding.toMap + (name + "'" -> rhsCell))) // bind the cell to the name

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
