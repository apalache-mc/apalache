package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, DefaultValueFactory, OracleHelper}
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
  private val pickRule = new CherryPick(rewriter)
  private val defaultValueFactory = new DefaultValueFactory(rewriter)

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
        def solverAssert = rewriter.solverContext.assertGroundExpr _
        // compute set comprehension and then pick an element from it
        val filterEx = tla.filter(varName, set, pred)
        var nextState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(filterEx))
        // pick an arbitrary witness
        val setCell = nextState.asCell
        if (nextState.arena.getHas(setCell).isEmpty) {
          rewriter.coerce(defaultValueFactory.makeUpValue(nextState, setCell), state.theory)
        } else {
          val elems = nextState.arena.getHas(setCell)
          val nelems = elems.size
          // add an oracle \in 0..N, where the indices from 0 to N - 1 correspond to the set elements,
          // whereas the index N corresponds to the default choice when the set is empty
          val (oracleState, oracle) = pickRule.oracleFactory.newPropositionalOracle(nextState, elems.size + 1)
          nextState = oracleState

          // pick a cell
          nextState = pickRule.pickByOracle(nextState, oracle, elems, nextState.arena.cellTrue().toNameEx)
          val pickedCell = nextState.asCell
          // require the oracle to produce only the values for the set elements (or no elements, when it is empty)
          OracleHelper.assertOraclePicksSetMembers(rewriter, nextState, oracle, setCell, elems)

          // If oracle = N, the picked cell is not constrained. In the past, we used a default value here,
          // but it sometimes produced conflicts (e.g., a picked record domain had to coincide with a default domain)
          rewriter.coerce(nextState.setRex(pickedCell.toNameEx), state.theory)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

}
