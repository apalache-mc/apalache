package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, FixedElemPtr, PureArena}
import at.forsyte.apalache.tla.lir.{IntT1, SetT1}
import at.forsyte.apalache.tla.types.tla

/**
 * Cache ranges a..b and, as a special case, tuple domains.
 *
 * @author
 *   Jure Kukovec
 */
class IntRangeCache(intValueCache: IntValueCache) extends Cache[PureArena, (Int, Int), (ArenaCell, Seq[ArenaCell])] {

  /**
   * Given a range as a boundary-pair `(a,b)`, returns a tuple `(rArena, (rCell, rCells))`, where:
   *   - `rCell` is the cell representing the set `a..b`
   *   - `rCells` is s sequence of cells `c_a, c_{a+1},..., c_b`, representing the range contents, i.e. `a, a+1, ...,
   *     b`.
   *   - `rArena` is an extension of `arena`, containing all of the above cells, and a relation
   *     {{{rCell --(has)--> c_a, c_{a+1},..., c_b}}}
   *
   * Note that this method internally calls `intValueCache.getOrCreate`, which caches all integers in the range.
   *
   * If `a > b`, we treat the input as if `range` were `(1,0)`, regardless of the concrete values of `a` and `b`, which
   * caches all empty ranges to the same value.
   */
  override protected def create(arena: PureArena, range: (Int, Int)): (PureArena, (ArenaCell, Seq[ArenaCell])) = {

    // We normalize a..b, such that, if the initial a is greater than b (which would give an empty range),
    // we always use 1..0. This lets us cache _all_ empty ranges into one cell.
    val (iFrom, iTo) = if (range._1 > range._2) (1, 0) else range

    val (arenaWithCachedInts, allCells) =
      iFrom.to(iTo).foldLeft((arena, Seq.empty[ArenaCell])) { case ((partialArena, partialCells), key) =>
        val (newArena, cell) = intValueCache.getOrCreate(partialArena, key)
        (newArena, partialCells :+ cell)
      }
    // create the domain cell
    val arenaWithDomCell = arenaWithCachedInts.appendCell(CellT.fromType1(SetT1(IntT1)))
    val setCell = arenaWithDomCell.topCell
    val arenaWithHas = arenaWithDomCell.appendHas(setCell, allCells.map(FixedElemPtr): _*)

    (arenaWithHas, (setCell, allCells))
  }

  /** Return a function to add implementation-specific constraints for a single entry */
  override def addConstraintsForElem(ctx: SolverContext): (((LevelT, LevelT), (ArenaCell, Seq[ArenaCell]))) => Unit = {
    case (_, (setCell, elemCells)) =>
      elemCells.foreach { elemCell =>
        // We _know_ the pointer is fixed TRUE by construction, so instead of asserting X == true, we just assert X, where
        // X = elemCell \in setCell
        ctx.assertGroundExpr(tla.in(elemCell.toBuilder, setCell.toBuilder))
      }
  }
}
