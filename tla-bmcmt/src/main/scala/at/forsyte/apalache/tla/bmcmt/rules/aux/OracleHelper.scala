package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.ConstT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, CellTheory, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla

/**
  * A helper class to create oracle values and compare them. Previously, we were using integers.
  * Now we are using uninterpreted constants. This may change again in the future.
  *
  * @author Igor Konnov
  */
class OracleHelper(val rewriter: SymbStateRewriter) {
  /**
    * Intoduce an integer oracle variable over 0..N-1, where the indices from 0 to N - 1 correspond to the set elements.
    * This method does not add any constraints on the contents of the set, you can do it by calling constrainOracleWithIn.
    * Nor it defines the default value. It is up to the specific operator how it is done.
    *
    * @param state
    * @param nelems the number of elements to choose from
    * @return a new symbolic state whose expression contains the oracle variable
    */
  def newOracleNoDefault(state: SymbState, nelems: Int): SymbState = {
    // add an oracle \in 0..N, where the indices from 0 to N - 1 correspond to the set elements
    val solverAssert = rewriter.solverContext.assertGroundExpr _
    var nextState = state.setArena(state.arena.appendCell(ConstT()))
    val oracle = nextState.arena.topCell.toNameEx
    def numToConst(i: Int): ArenaCell = {
      val (newArena, indexConst) = rewriter.strValueCache.getOrCreate(nextState.arena, i.toString)
      nextState = nextState.setArena(newArena)
      indexConst
    }

    val nums = 0.until(nelems) map numToConst
    solverAssert(tla.or(nums.map(c => tla.eql(c.toNameEx, oracle)) :_*))
    nextState.setRex(oracle).setTheory(CellTheory())
  }

  /**
    * Intoduce an integer oracle variable over 0..N, where the indices from 0 to N - 1 correspond to the set elements,
    * whereas the index N corresponds to the default choice when the set is empty. This method does not add any
    * constraints on the contents of the set, you can do it by calling constrainOracleWithIn.
    * Nor it defines the default value. It is up to the specific operator how it is done.
    *
    * @param state
    * @param nelems the number of elements to choose from
    * @return a new symbolic state whose expression contains the oracle variable
    */
  def newOracleWithDefault(state: SymbState, nelems: Int): SymbState = {
    newOracleNoDefault(state, nelems + 1)
  }

  def getOracleValue(state: SymbState, num: Int): ArenaCell = {
    val strVal = rewriter.strValueCache.get(num.toString)
    assert(strVal.isDefined)
    strVal.get
  }

  def oracleEqTo(state: SymbState, oracle: TlaEx, num: Int): TlaEx = {
    tla.eql(oracle, getOracleValue(state, num).toNameEx)
  }

  /**
    * <p>Add the following constraints:</p>
    *
    * <ul>
    *   <li>oracle = i > in(e_i, S) for 0 <= i < N, and</li>
    *   <li>oracle = N => \A i \in 0..(N-1) ~in(e_i, S).</li>
    * </ul>
    *
    * <p>It is often natural to add these constraints. Sometimes, these constraints come in a different form.</p>
    *
    * @param oracle an oracle that is created with newOracleWithDefault
    * @param set a set cell
    * @param setElems the cells pointed by the set
    */
  def constrainOracleWithIn(state: SymbState, oracle: ArenaCell, set: ArenaCell, setElems: Seq[ArenaCell]): Unit = {
    def chooseWhenIn(el: ArenaCell, no: Int): Unit = {
      val chosen = tla.eql(oracle.toNameEx, getOracleValue(state, no).toNameEx)
      val in = tla.in(el.toNameEx, set.toNameEx)
      rewriter.solverContext.assertGroundExpr(tla.impl(chosen, in))
    }

    // 1. oracle = i > in(e_i, S) for 0 <= i < N
    setElems.zipWithIndex foreach (chooseWhenIn _).tupled
    // 2. oracle = N => \A i \in 0..(N-1) ~in(e_i, S)
    val allNotIn = tla.and(setElems map (e => tla.not(tla.in(e.toNameEx, set.toNameEx))) :_*)
    val defaultChosen = tla.eql(oracle.toNameEx, getOracleValue(state, setElems.size).toNameEx)
    rewriter.solverContext.assertGroundExpr(tla.impl(defaultChosen, allNotIn))
  }

}
