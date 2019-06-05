package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.ConstT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, CellTheory, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla

/**
  * A helper class to create oracle values and compare them. In two previous solutions, we were
  * using integers, then uninterpreted constants. Now we are using just propositional variables.
  * This may change again in the future.
  *
  * @author Igor Konnov
  */
object OracleHelper {
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
    * @param rewriter a state rewriter
    * @param oracle an oracle that is created with newOracleWithDefault
    * @param set a set cell
    * @param setElems the cells pointed by the set
    */
  def constrainOracleWithIn(rewriter: SymbStateRewriter, state: SymbState,
                            oracle: Oracle, set: ArenaCell, setElems: Seq[ArenaCell]): Unit = {
    def chooseWhenIn(el: ArenaCell, no: Int): Unit = {
      val chosen = oracle.oracleEqTo(state, no)
      val in = tla.in(el.toNameEx, set.toNameEx)
      rewriter.solverContext.assertGroundExpr(tla.impl(chosen, in))
    }

    // 1. oracle = i > in(e_i, S) for 0 <= i < N
    setElems.zipWithIndex foreach (chooseWhenIn _).tupled
    // 2. oracle = N => \A i \in 0..(N-1) ~in(e_i, S)
    val allNotIn = tla.and(setElems map (e => tla.not(tla.in(e.toNameEx, set.toNameEx))) :_*)
    val defaultChosen = oracle.oracleEqTo(state, setElems.size)
    rewriter.solverContext.assertGroundExpr(tla.impl(defaultChosen, allNotIn))
  }

}
