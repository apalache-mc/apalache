package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell}
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, IntT}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Cache tuple domains as well as ranges a..b.
 *
 * @author Igor Konnov
 */
class IntRangeCache(solverContext: SolverContext, intValueCache: IntValueCache)
    extends AbstractCache[Arena, (Int, Int), ArenaCell] with Serializable {

  /**
   * Create a set a..b.
   *
   * @param context  the context before creating a new value
   * @param range a constant integer range
   * @return a target value that is going to be cached and the new context
   */
  override def create(context: Arena, range: (Int, Int)): (Arena, ArenaCell) = {
    var arena = context
    def intToCell(i: Int): ArenaCell = {
      val (newArena, cell) = intValueCache.getOrCreate(arena, i)
      arena = newArena
      cell
    }

    val cells = range._1.to(range._2) map intToCell
    // create the domain cell
    arena = arena.appendCell(FinSetT(IntT()))
    val set = arena.topCell
    arena = arena.appendHas(set, cells: _*)
    // force that every element is in the set
    solverContext.assertGroundExpr(tla.and(cells.map(c => tla.in(c.toNameEx, set.toNameEx)): _*))
    (arena, set)
  }
}
