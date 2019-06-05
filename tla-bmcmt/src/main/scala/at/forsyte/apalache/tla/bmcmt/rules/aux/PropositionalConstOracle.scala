package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla


class PropositionalConstOracle(bitCells: Seq[ArenaCell]) extends Oracle {
  /**
    * Produce an expression that states that the oracle values equals to the given integer position.
    * The actual implementation may be different from an integer comparison.
    *
    * @param state    a symbolic state
    * @param position a position the oracle should be equal to
    */
  override def oracleEqTo(state: SymbState, position: Int): TlaEx = {
    def mkLits(n: Int, cells: Seq[ArenaCell]): Seq[TlaEx] = {
      cells match {
        case Nil => Nil

        case hd +: tl =>
          val lit =
            if ((n & 1) == 1) hd.toNameEx else tla.not(hd.toNameEx)
          lit +: mkLits(n >> 1, tl)
      }
    }

    bitCells.size match {
      case 0 => state.arena.cellTrue().toNameEx

      case 1 => mkLits(position, bitCells).head

      case _ => tla.and(mkLits(position, bitCells) :_*)
    }
  }
}

object PropositionalConstOracle {
  def create(rewriter: SymbStateRewriter, state: SymbState, nvalues: Int): (SymbState, Oracle) = {
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
    val (newArena, newCells) = state.arena.appendCellSeq(0 until nbits map (_ => BoolT()) :_*)
    val oracle = new PropositionalConstOracle(newCells)
    var nextState = state.setArena(newArena)

    // exclude the values that are above nvalues
    def pow(n: Int): Int = if (n <= 0) 1 else 2 * pow(n - 1)
    val upperBound = pow(nbits)

    for (i <- nvalues until upperBound) {
      solverAssert(tla.not(oracle.oracleEqTo(nextState, i)))
    }

    (nextState, oracle)
  }
}