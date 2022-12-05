package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.arena.{ElemPtr, FixedElemPtr, PureArenaAdapter}
import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.{IntT1, SetT1}
import at.forsyte.apalache.tla.types.tla

/**
 * Cache tuple domains as well as ranges a..b.
 *
 * @author
 *   Igor Konnov
 */
class IntRangeCache(solverContext: SolverContext, intValueCache: IntValueCache)
    extends AbstractCache[PureArenaAdapter, (Int, Int), ArenaCell] with Serializable {

  /**
   * Create a set a..b.
   *
   * @param context
   *   the context before creating a new value
   * @param range
   *   a constant integer range
   * @return
   *   a target value that is going to be cached and the new context
   */
  override def create(context: PureArenaAdapter, range: (Int, Int)): (PureArenaAdapter, ArenaCell) = {
    var arena = context
    def intToCell(i: Int): ElemPtr = {
      val (newArena, cell) = intValueCache.getOrCreate(arena, i)
      arena = newArena
      FixedElemPtr(cell, true)
    }

    val cells = range._1.to(range._2).map(intToCell)
    // create the domain cell
    arena = arena.appendCell(SetT1(IntT1))
    val set = arena.topCell
    arena = arena.appendHas(set, cells: _*)
    // force that every element is in the set
    // TODO: Use fixed pointers in lieu of storeInSet.
    for (cell <- cells) solverContext.assertGroundExpr(tla.storeInSet(cell.elem.toBuilder, set.toBuilder))
    (arena, set)
  }
}
