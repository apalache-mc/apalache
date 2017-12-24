package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}


/**
  * Implements the rules: SE-ASSIGN{1,2,3}.
  * Similar to TLC, this is a special form of x \in S operator that is treated
  * as an assignment of a value from S to the variable x.
  *
  * TODO: add support for tuples!
  *
  * @author Igor Konnov
  */
class AssignmentRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickRule = new PickFromAndFunMerge(rewriter)

  override def isApplicable(state: SymbState): Boolean = {
    def isUnbound(name: String) =
      (!CellTheory().hasConst(name)
        && !BoolTheory().hasConst(name)
        && !IntTheory().hasConst(name)
        && !state.binding.contains(name + "'"))

    state.ex match {
      case OperEx(TlaSetOper.in, OperEx(TlaActionOper.prime, NameEx(name)), _) =>
        isUnbound(name)

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      // a common pattern x' \in {y} that deterministically assigns the value of y to x'
      case OperEx(TlaSetOper.in,
          OperEx(TlaActionOper.prime, NameEx(name)),
          OperEx(TlaSetOper.enumSet, rhs)) =>
        val nextState = rewriter.rewriteUntilDone(state.setRex(rhs).setTheory(CellTheory()))
        val rhsCell = nextState.arena.findCellByNameEx(nextState.ex)
        val finalState = nextState
          .setTheory(BoolTheory())
          .setRex(NameEx(rewriter.solverContext.trueConst))
          .setBinding(nextState.binding + (name + "'" -> rhsCell)) // bind the cell to the name
        rewriter.coerce(finalState, state.theory)

      // the general case
      case OperEx(TlaSetOper.in,
                  OperEx(TlaActionOper.prime, NameEx(name)),
                  set) =>
        // switch to cell theory
        val setState = rewriter.rewriteUntilDone(state.setRex(set))
        val setCell = setState.arena.findCellByNameEx(setState.ex)
        // pick an arbitrary witness
        val pickState = pickRule.pick(setCell, setState)
        val pickedCell = pickState.arena.findCellByNameEx(pickState.ex)
        val finalState = pickState
          .setTheory(BoolTheory())
          .setRex(NameEx(rewriter.solverContext.trueConst))
          .setBinding(pickState.binding + (name + "'" -> pickedCell)) // bind the picked cell to the name

        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
