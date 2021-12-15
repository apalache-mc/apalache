package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, arraysEncoding}
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, IntT}
import at.forsyte.apalache.tla.lir.{BuilderEx, ValEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.values.TlaBool

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
    if (solverContext.config.smtEncoding == arraysEncoding) {
      def addCons(cells: Seq[ArenaCell]): BuilderEx = {
        val c = cells.head

        cells.tail match {
          case Seq() => tla.apalacheStoreInSetOneStep(c.toNameEx, set.toNameEx, ValEx(TlaBool(true)))
          case tail  => tla.apalacheStoreInSetOneStep(c.toNameEx, addCons(tail), ValEx(TlaBool(true)))
        }
      }

      if (cells.nonEmpty) {
        val cons = addCons(cells)
        solverContext.assertGroundExpr(tla.apalacheStoreInSetLastStep(set.toNameEx, cons))
      }
    } else {
      solverContext.assertGroundExpr(tla.and(cells.map(c => tla.apalacheStoreInSet(c.toNameEx, set.toNameEx)): _*))
    }
    (arena, set)
  }
}
