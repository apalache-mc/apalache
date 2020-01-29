package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, OracleHelper}
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, FinFunSetT, FinSetT, PowSetT}
import at.forsyte.apalache.tla.lir.oper.{BmcOper, TlaActionOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}
import at.forsyte.apalache.tla.lir.convenience.tla

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
      (!CellTheory().hasConst(name)
        && !BoolTheory().hasConst(name)
        && !IntTheory().hasConst(name)
        && !state.binding.contains(name + "'"))

    state.ex match {
      case OperEx(BmcOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), _) =>
        isUnbound(name)

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      // general case
      case OperEx(BmcOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), rhs) =>
        val nextState = rewriter.rewriteUntilDone(state.setRex(rhs).setTheory(CellTheory()))
        val rhsCell = nextState.arena.findCellByNameEx(nextState.ex)
        val finalState = nextState
          .setTheory(CellTheory())
          .setRex(state.arena.cellTrue().toNameEx) // just return TRUE
          .setBinding(nextState.binding + (name + "'" -> rhsCell)) // bind the cell to the name
        rewriter.coerce(finalState, state.theory)
      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
