package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, OracleHelper}
import at.forsyte.apalache.tla.lir.{OperEx, SetT1}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper

/**
 * <p>Rewriting rule for CHOOSE. Similar to TLC, we implement a non-deterministic choice. It is not hard to add the
 * requirement of determinism, but that will most likely affect efficiency.</p>
 *
 * <p>TODO: add determinism as an option.</p>
 *
 * @author
 *   Igor Konnov
 */
class ChooseRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickRule = new CherryPick(rewriter)

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
        // This is a general encoding, handling both happy and unhappy scenarios,
        // that is, when CHOOSE is defined on its arguments and not, respectively.

        // compute set comprehension and then pick an element from it
        val setT = set.typeTag.asTlaType1()
        val filterEx = tla
          .filter(varName, set, pred)
          .typed(setT)
        var nextState = rewriter.rewriteUntilDone(state.setRex(filterEx))
        // pick an arbitrary witness
        val setCell = nextState.asCell
        if (nextState.arena.getHas(setCell).isEmpty) {
          setT match {
            case SetT1(elemT) =>
              val (stateAfter, _) = rewriter.defaultValueCache.getOrCreate(nextState, elemT)
              stateAfter

            case _ =>
              throw new IllegalStateException(s"Expected a set, found: $setT")
          }
        } else {
          val elems = nextState.arena.getHas(setCell)
          // add an oracle \in 0..N, where the indices from 0 to N - 1 correspond to the set elements,
          // whereas the index N corresponds to the default choice when the set is empty
          val (oracleState, oracle) = pickRule.oracleFactory.newDefaultOracle(nextState, elems.size + 1)
          nextState = oracleState

          // pick a cell
          nextState = pickRule.pickByOracle(nextState, oracle, elems, nextState.arena.cellTrue().toNameEx)
          val pickedCell = nextState.asCell
          // require the oracle to produce only the values for the set elements (or no elements, when it is empty)
          OracleHelper.assertOraclePicksSetMembers(rewriter, nextState, oracle, setCell, elems)

          // If oracle = N, the picked cell is not constrained. In the past, we used a default value here,
          // but it sometimes produced conflicts (e.g., a picked record domain had to coincide with a default domain)
          nextState.setRex(pickedCell.toNameEx)
        }

      // once the issue #95 has been resolved, use happyChoose

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  // This translation is sound only in the happy scenario, that is, when CHOOSE is defined on its argument.
  // It should be used only after resolving the issue #95: https://github.com/informalsystems/apalache/issues/95

}
