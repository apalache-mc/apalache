package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.CellTFrom
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

class PropositionalOracle(bitCells: Seq[ArenaCell], nvalues: Int) extends Oracle {

  override def size: Int = nvalues

  override def whenEqualTo(state: SymbState, position: Int): TBuilderInstruction = {
    def mkLits(n: Int, cells: Seq[ArenaCell]): Seq[TBuilderInstruction] = {
      cells match {
        case Nil => Nil

        case hd +: tl =>
          // the least significant bit comes first
          val lit =
            if ((n & 1) == 1) hd.toBuilder else tla.not(hd.toBuilder)
          lit +: mkLits(n >> 1, tl)
      }
    }

    bitCells.size match {
      case 0 => state.arena.cellTrue().toBuilder

      case 1 => mkLits(position, bitCells).head

      case _ => tla.and(mkLits(position, bitCells): _*)
    }
  }

  override def caseAssertions(
      state: SymbState,
      assertions: Seq[TBuilderInstruction],
      elseAssertions: Seq[TBuilderInstruction] = Seq.empty): TBuilderInstruction = {
    if (elseAssertions.nonEmpty & assertions.size != elseAssertions.size) {
      throw new IllegalStateException(s"Invalid call to Oracle, malformed elseAssertions")
    }

    super.caseAssertions(state, assertions, elseAssertions)
  }

  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = {
    def cellsToInt(bits: Seq[ArenaCell]): Int = {
      bits match {
        case Nil => 0

        case lsbCell :: otherBitCells =>
          // find the value of the bit, which is the least significant
          val isOn = solverContext.evalGroundExpr(lsbCell.toBuilder) == tla.bool(true).build
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
    val (newArena, newCells) = state.arena.appendCellSeq((0 until nbits).map(_ => CellTFrom(BoolT1)): _*)
    val oracle = new PropositionalOracle(newCells, nvalues)
    val nextState = state.setArena(newArena)

    // exclude the values that are above nvalues
    def pow(n: Int): Int = if (n <= 0) 1 else 2 * pow(n - 1)
    val upperBound = pow(nbits)

    for (i <- nvalues until upperBound) {
      solverAssert(tla.not(oracle.whenEqualTo(nextState, i)))
    }

    (nextState, oracle)
  }
}
