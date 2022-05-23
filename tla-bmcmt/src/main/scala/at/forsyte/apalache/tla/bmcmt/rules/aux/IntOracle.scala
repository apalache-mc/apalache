package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState}
import at.forsyte.apalache.tla.lir.{IntT1, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

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

  override def size: Int = nvalues

  override def whenEqualTo(state: SymbState, position: Int): TlaEx = {
    tla.eql(intCell.toNameEx, tla.int(position))
  }

  override def caseAssertions(state: SymbState, assertions: Seq[TlaEx], elseAssertions: Seq[TlaEx] = Seq()): TlaEx = {
    if (elseAssertions.nonEmpty && assertions.size != elseAssertions.size) {
      throw new IllegalStateException(s"Invalid call to Oracle, malformed elseAssertions")
    }

    super.caseAssertions(state, assertions, elseAssertions)
  }

  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = {
    solverContext.evalGroundExpr(intCell.toNameEx).asInstanceOf[Int]
  }
}

object IntOracle {
  def create(state: SymbState, nvalues: Int): (SymbState, IntOracle) = {
    val nextState = state.setArena(state.arena.appendCell(IntT1))
    val oracleCell = nextState.arena.topCell
    val oracle = new IntOracle(oracleCell, nvalues)
    // the oracle value must be equal to one of the value cells
    (nextState, oracle)
  }
}
