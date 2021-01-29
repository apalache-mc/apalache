package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, DefaultValueFactory, OracleHelper}
import at.forsyte.apalache.tla.bmcmt.types.FinSetT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}


/**
  * <p>Rewriting rule for CHOOSE. Similar to TLC, we implement a non-deterministic choice.
  * It is not hard to add the requirement of determinism, but that will most likely affect efficiency.</p>
  *
  * <p>TODO: add determinism as an option.</p>
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
        // This is a general encoding, handling both happy and unhappy scenarios,
        // that is, when CHOOSE is defined on its arguments and not, respectively.
        def solverAssert = rewriter.solverContext.assertGroundExpr _
        // compute set comprehension and then pick an element from it
        val filterEx = tla.filter(varName, set, pred)
        var nextState = rewriter.rewriteUntilDone(state.setRex(filterEx))
        // pick an arbitrary witness
        val setCell = nextState.asCell
        if (nextState.arena.getHas(setCell).isEmpty) {
          defaultValueFactory.makeUpValue(nextState, setCell)
        } else {
          val elems = nextState.arena.getHas(setCell)
          val nelems = elems.size
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
  private def happyChoose(state: SymbState, varName: String, set: TlaEx, pred: TlaEx): SymbState = {
    // rewrite the bounding set
    val nextState = rewriter.rewriteUntilDone(state.setRex(set))
    val setCell = nextState.asCell
    val isFinSet = PartialFunction.cond(setCell.cellType) { case FinSetT(_) => true }
    if (isFinSet) {
      happyChooseFromFinite(nextState, setCell, varName, pred)
    } else {
      happyChooseFromOther(nextState, setCell, varName, pred)
    }
  }

  private def happyChooseFromFinite(state: SymbState, setCell: ArenaCell, varName: String, pred: TlaEx): SymbState = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _

    if (state.arena.getHas(setCell).isEmpty) {
      defaultValueFactory.makeUpValue(state, setCell)
    } else {
      val elems = state.arena.getHas(setCell)
      var (nextState, oracle) = pickRule.oracleFactory.newDefaultOracle(state, elems.size)
      val trueEx = nextState.arena.cellTrue().toNameEx

      // pick only the elements that belong to the set
      val elemsIn = elems map { e => tla.in(e.toNameEx, setCell.toNameEx) }
      solverAssert(oracle.caseAssertions(nextState, elemsIn))
      nextState = pickRule.pickByOracle(nextState, oracle, elems, trueEx)
      val witness = nextState.asCell
      // assert that the predicate holds -- we are in the happy case
      val tempBinding = Binding(nextState.binding.toMap + (varName -> witness))
      nextState = rewriter.rewriteUntilDone(nextState.setRex(pred).setBinding(tempBinding))
      solverAssert(nextState.ex)
      // return the witness
      nextState.setRex(witness.toNameEx).setBinding(Binding(nextState.binding.toMap - varName))
    }
  }

  private def happyChooseFromOther(state: SymbState, setCell: ArenaCell, varName: String, pred: TlaEx): SymbState = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _

    // the set is never empty, e.g., a powerset or a function set
    var nextState = pickRule.pick(setCell, state, state.arena.cellFalse().toNameEx)
    val witness = nextState.asCell
    // assert that the witness satisfies the predicate -- we are in the happy case
    val tempBinding = Binding(nextState.binding.toMap + (varName -> witness))
    nextState = rewriter.rewriteUntilDone(nextState.setRex(pred).setBinding(tempBinding))
    solverAssert(nextState.ex)
    // return the witness
    nextState.setRex(witness.toNameEx).setBinding(Binding(nextState.binding.toMap - varName))
  }

}
