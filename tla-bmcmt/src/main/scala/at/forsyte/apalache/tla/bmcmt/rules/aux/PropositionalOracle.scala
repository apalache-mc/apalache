package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla

class PropositionalOracle(bitCells: Seq[ArenaCell], nvalues: Int) extends Oracle {

  /**
   * Produce an expression that states that the oracle values equals to the given integer position.
   * The actual implementation may be different from an integer comparison.
   *
   * @param state    a symbolic state
   * @param position a position the oracle should be equal to
   */
  override def whenEqualTo(state: SymbState, position: Int): TlaEx = {
    def mkLits(n: Int, cells: Seq[ArenaCell]): Seq[TlaEx] = {
      cells match {
        case Nil => Nil

        case hd +: tl =>
          // the least significant bit comes first
          val lit =
            if ((n & 1) == 1) hd.toNameEx else tla.not(hd.toNameEx)
          lit +: mkLits(n >> 1, tl)
      }
    }

    bitCells.size match {
      case 0 => state.arena.cellTrue().toNameEx

      case 1 => mkLits(position, bitCells).head

      case _ => tla.and(mkLits(position, bitCells): _*)
    }
  }

  /**
   * Produce a ground expression that contains assertions for the possible oracle values.
   *
   * @param state      a symbolic state
   * @param assertions a sequence of assertions, one per oracle value
   * @return an expression ite(oracle = 0, ite(oracle = 1, ...))
   */
  override def caseAssertions(state: SymbState, assertions: Seq[TlaEx]): TlaEx = {
    nvalues match {
      case 0 => state.arena.cellTrue().toNameEx

      case 1 => assertions.head

      case _ =>
        val es = assertions
          .slice(0, nvalues)
          .zipWithIndex
          .map { case (e, i) => tla.or(e, tla.not(whenEqualTo(state, i))) }
        tla.and(es: _*)
    }
  }

  /**
   * Get a symbolic state and decode the value of the oracle variable into an integer.
   * This method assumes that the solver context has produced an SMT model.
   *
   * @param solverContext a solver context
   * @param state         a symbolic state
   * @return an integer value of the oracle
   */
  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = {
    def cellsToInt(bits: Seq[ArenaCell]): Int = {
      bits match {
        case Nil => 0

        case lsbCell :: otherBitCells =>
          // find the value of the bit, which is the least significant
          val isOn = solverContext.evalGroundExpr(lsbCell.toNameEx) == tla.bool(true)
          val lsb = if (isOn) 1 else 0
          // find the unsigned integer value
          lsb + 2 * cellsToInt(otherBitCells) // the bits to the right are more significant
      }
    }

    cellsToInt(bitCells)
  }
}

object PropositionalOracle {
  def create(rewriter: SymbStateRewriter, state: SymbState, nvalues: Int): (SymbState, PropositionalOracle) = {
    val solverAssert = rewriter.solverContext.assertGroundExpr _

    // how many bits do we need to fit n values
    def findNBits(n: Int): Int = {
      if (n >= nvalues) {
        0
      } else {
        1 + findNBits(2 * n)
      }
    }

    val nbits = findNBits(1)
    // create nbits cells to hold the propositional variables
    val (newArena, newCells) = state.arena.appendCellSeq(0 until nbits map (_ => BoolT()): _*)
    val oracle = new PropositionalOracle(newCells, nvalues)
    var nextState = state.setArena(newArena)

    // exclude the values that are above nvalues
    def pow(n: Int): Int = if (n <= 0) 1 else 2 * pow(n - 1)
    val upperBound = pow(nbits)

    for (i <- nvalues until upperBound) {
      solverAssert(tla.not(oracle.whenEqualTo(nextState, i)))
    }

    (nextState, oracle)
  }
}
