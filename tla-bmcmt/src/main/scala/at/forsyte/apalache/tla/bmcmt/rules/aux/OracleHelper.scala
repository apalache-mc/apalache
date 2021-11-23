package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

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
  def assertOraclePicksSetMembers(rewriter: SymbStateRewriter, state: SymbState, oracle: Oracle, set: ArenaCell,
      setElems: Seq[ArenaCell]): Unit = {
    val inOperFactory: InOpFactory = new InOpFactory(rewriter.solverContext.config.smtEncoding)

    val elemsIn = setElems map { e => inOperFactory.mkAccessOp(e, set).untyped() }
    val allNotIn = tla.and(setElems map (e => tla.not(inOperFactory.mkAccessOp(e, set))): _*).untyped()
    rewriter.solverContext.assertGroundExpr(oracle.caseAssertions(state, elemsIn :+ allNotIn))
  }

}
