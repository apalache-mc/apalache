package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.oracles

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches.UninterpretedLiteralCache
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{Rewriter, RewriterScope}
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.ConstT1
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * An oracle that uses a fixed collection of potential cells.
 *
 * The oracle value must be equal to one of the cells, if the collection is nonempty.
 *
 * @author
 *   Jure Kukovec
 */
class UninterpretedConstOracle(val valueCells: Seq[ArenaCell], val oracleCell: ArenaCell) extends Oracle {

  /**
   * The number of values that this oracle is defined over: |valueCells|
   */
  override def size: Int = valueCells.size

  override def chosenValueIsEqualToIndexedValue(scope: RewriterScope, index: BigInt): TBuilderInstruction =
    if (valueCells.indices.contains(index)) tla.eql(oracleCell.toBuilder, valueCells(index.toInt).toBuilder)
    else tla.bool(false)

  def getIndexOfChosenValueFromModel(solverContext: SolverContext): BigInt =
    // the oracle must be equal to one of the values. If not, indexWhere returns -1
    valueCells.indexWhere { valueCell =>
      val eq = tla.eql(valueCell.toBuilder, oracleCell.toBuilder)
      solverContext.evalGroundExpr(eq) == tla.bool(true).build
    }
}

object UninterpretedConstOracle {

  /**
   * Designated type to be used in this oracle.
   */
  val UNINTERPRETED_TYPE: ConstT1 = ConstT1("_ORA")

  def create(
      rewriter: Rewriter,
      cache: UninterpretedLiteralCache,
      scope: RewriterScope,
      nvalues: Int): (RewriterScope, UninterpretedConstOracle) = {
    require(nvalues >= 0, "UninterpretedConstOracle must have a non-negative number of candidate values.")
    val (newArena, valueCells) =
      0.until(nvalues).map(_.toString).foldLeft((scope.arena, Seq.empty[ArenaCell])) { case ((arena, cells), name) =>
        val (newArena, newCell) = cache.getOrCreate(arena, (UNINTERPRETED_TYPE, name))
        (newArena, cells :+ newCell)
      }
    val arenaWithCell = newArena.appendCell(CellT.fromType1(UNINTERPRETED_TYPE))
    val newScope = scope.copy(arena = arenaWithCell)
    val oracleCell = arenaWithCell.topCell
    val oracle = new UninterpretedConstOracle(valueCells, oracleCell)

    // the oracle value must be equal to one of the value cells, if there are any
    if (nvalues > 0)
      rewriter.assert(tla.or(0.until(nvalues).map(i => oracle.chosenValueIsEqualToIndexedValue(newScope, i)): _*))
    (newScope, oracle)
  }
}
