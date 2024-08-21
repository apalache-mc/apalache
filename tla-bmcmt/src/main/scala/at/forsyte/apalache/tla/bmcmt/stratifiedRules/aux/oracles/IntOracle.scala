package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles
import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.{IntT1, ValEx}
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}

/**
 * An oracle that uses an integer variable. Although using integers as an oracle is the most straightforward decision,
 * whenever a specialized oracle is available, it should be used instead, for performance reasons.
 *
 * @author
 *   Jure Kukovec
 */
class IntOracle(val intCell: ArenaCell, nvalues: Int) extends Oracle {
  require(nvalues >= 0, "IntOracle must have a non-negative number of candidate values.")

  /**
   * The number of values that this oracle is defined over: `0..(size - 1)`.
   */
  override def size: Int = nvalues

  /**
   * Produce an expression that states that the chosen value equals to the value `v_{index}`. The actual implementation
   * may be different from an integer comparison.
   */
  override def chosenValueIsEqualToIndexedValue(scope: RewriterScope, index: BigInt): BuilderT =
    tla.eql(intCell.toBuilder, tla.int(index))

  override def getIndexOfChosenValueFromModel(solverContext: SolverContext): BigInt =
    solverContext.evalGroundExpr(intCell.toBuilder) match {
      case ValEx(TlaInt(i)) => i
      case _ => throw new IllegalStateException(s"Invalid call to \"getIndexOfOracleValueFromModel\", not an integer.")
    }

}

object IntOracle {
  def create(scope: RewriterScope, nvalues: Int): (RewriterScope, IntOracle) = {
    val newArena = scope.arena.appendCell(CellT.fromType1(IntT1))
    val oracleCell = newArena.topCell
    val oracle = new IntOracle(oracleCell, nvalues)
    // the oracle value must be equal to one of the value cells
    (scope.copy(arena = newArena), oracle)
  }
}
