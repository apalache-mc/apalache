package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, FixedElemPtr, PureArena}
import at.forsyte.apalache.tla.lir.{SetT1, StrT1}
import at.forsyte.apalache.tla.types.tla

import scala.collection.immutable.SortedSet

/**
 * Since we have to create record domains many times, we cache them here.
 *
 * @author
 *   Jure Kukovec
 */
class RecordDomainCache(strValueCache: UninterpretedLiteralCache)
    extends Cache[PureArena, SortedSet[String], (ArenaCell, Seq[ArenaCell])] {

  /**
   * Given a set of `keys`, returns a tuple `(rArena, (rCell, rCells))`, where:
   *   - `rCell` is the cell representing the set `keys`
   *   - `rCells` is s sequence of cells `c_1, c_2,..., c_|keys|`, representing the set contents (e.g. "a", "b", ...).
   *   - `rArena` is an extension of `arena`, containing all of the above cells, and a relation
   *     {{{rCell --(has)--> c_1, c_2,..., c_|keys|}}}
   *
   * Note that this method internally calls `strValueCache.getOrCreate`, which caches all strings in the set.
   */
  override protected def create(
      arena: PureArena,
      keys: SortedSet[String]): (PureArena, (ArenaCell, Seq[ArenaCell])) = {

    val (arenaWithCachedStrs, allCells) = keys.toList.foldLeft((arena, Seq.empty[ArenaCell])) {
      case ((partialArena, partialCells), key) =>
        val (newArena, cell) = strValueCache.getOrCreate(partialArena, (StrT1, key))
        (newArena, partialCells :+ cell)
    }

    // create the domain cell
    val arenaWithDomCell = arenaWithCachedStrs.appendCell(CellT.fromType1(SetT1(StrT1)))
    val setCell = arenaWithDomCell.topCell
    val arenaWithHas = arenaWithDomCell.appendHas(setCell, allCells.map(FixedElemPtr): _*)

    (arenaWithHas, (setCell, allCells))
  }

  /** Return a function to add implementation-specific constraints for a single entry */
  override def addConstraintsForElem(ctx: SolverContext): ((SortedSet[String], (ArenaCell, Seq[ArenaCell]))) => Unit = {
    case (_, (setCell, elemCells)) =>
      elemCells.foreach { elemCell =>
        // We _know_ the pointer is fixed TRUE by construction, so instead of asserting X == true, we just assert X, where
        // X = elemCell \in setCell
        ctx.assertGroundExpr(tla.in(elemCell.toBuilder, setCell.toBuilder))
      }
  }
}
