package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.values.TlaBool

/**
 * An oracle that uses an integer variable. Although using integers as an oracle is the most straightforward decision,
 * do not use this oracle by default. It is handy, when reasoning about sequences.
 *
 * @author
 *   Igor Konnov
 *
 * @param intCell
 *   an integer cell to be used as the oracle
 * @param nvalues
 *   the of values to accommodate
 */
class IntOracle(val intCell: ArenaCell, nvalues: Int) extends Oracle {

  /**
   * Produce an expression that states that the oracle values equals to the given integer position. The actual
   * implementation may be different from an integer comparison.
   *
   * @param state
   *   a symbolic state
   * @param position
   *   a position the oracle should be equal to
   */
  override def whenEqualTo(state: SymbState, position: Int): TlaEx = {
    tla.eql(intCell.toNameEx, tla.int(position))
  }

  /**
   * Produce a ground expression that contains assertions for the possible oracle values.
   *
   * @param state
   *   a symbolic state
   * @param assertions
   *   a sequence of assertions, one per oracle value
   * @param elseAssertions
   *   an optional sequence of assertions, one per oracle value
   * @return
   *   an expression ite(oracle = 0, ite(oracle = 1, ...))
   */
  override def caseAssertions(state: SymbState, assertions: Seq[TlaEx], elseAssertions: Seq[TlaEx] = Seq()): TlaEx = {
    if (elseAssertions.nonEmpty & assertions.size != elseAssertions.size) {
      throw new IllegalStateException(s"Invalid call to Oracle, malformed elseAssertions")
    }

    nvalues match {
      case 0 => state.arena.cellTrue().toNameEx

      case 1 => assertions.head

      case _ =>
        // iteCases is a sequence of tuples, with the fst and snd elements of each tuple being the "if" and "else" cases of an ite.
        // If elseAssertions is not empty, each tuple has its fst element from assertions and its snd form elseAssertions.
        // If elseAssertions is empty, each tuple has its fst element from assertions and its snd defaults to "ValEx(TlaBool(true))".
        val iteCases = assertions.zipAll(elseAssertions, ValEx(TlaBool(true)), ValEx(TlaBool(true)))
        val es =
          iteCases.slice(0, nvalues).zipWithIndex.map { case (e, i) => tla.ite(whenEqualTo(state, i), e._1, e._2) }
        tla.and(es: _*)
    }
  }

  /**
   * Get a symbolic state and decode the value of the oracle variable into an integer. This method assumes that the
   * solver context has produced an SMT model.
   *
   * @param solverContext
   *   a solver context
   * @param state
   *   a symbolic state
   * @return
   *   an integer value of the oracle
   */
  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = {
    solverContext.evalGroundExpr(intCell.toNameEx).asInstanceOf[Int]
  }
}

object IntOracle {
  def create(rewriter: SymbStateRewriter, state: SymbState, nvalues: Int): (SymbState, IntOracle) = {
    val nextState = state.setArena(state.arena.appendCell(IntT()))
    val oracleCell = nextState.arena.topCell
    val oracle = new IntOracle(oracleCell, nvalues)
    // the oracle value must be equal to one of the value cells
    (nextState, oracle)
  }
}
