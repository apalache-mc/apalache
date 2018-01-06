package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{ConstT, FinSetT}
import at.forsyte.apalache.tla.lir.convenience.tla

import scala.collection.immutable.SortedSet

/**
  * Since we have to create record domains many times, we cache them here.
  *
  * @author Igor Konnov
  */
class RecordDomainCache(solverContext: SolverContext, strValueCache: StrValueCache)
  extends AbstractCache[Arena, SortedSet[String], ArenaCell] {

  /**
    * Create a set for a sorted set of record keys.
    *
    * @param context  the context before creating a new value
    * @param keySet a source value
    * @return a target value that is going to be cached and the new context
    */
  override def create(context: Arena, keySet: SortedSet[String]): (Arena, ArenaCell) = {
    var arena = context
    def strToCell(str: String): ArenaCell = {
      val (newArena, cell) = strValueCache.getOrCreate(arena, str)
      arena = newArena
      cell
    }

    val cells = keySet.toList map strToCell
    // create the domain cell
    arena = arena.appendCell(FinSetT(ConstT()))
    val set = arena.topCell
    arena = cells.foldLeft(arena) ((a, c) => a.appendHas(set, c))
    // force that every element is in the set
    solverContext.assertGroundExpr(tla.and(cells.map(tla.in(_, set)) :_*))
    (arena, set)
  }
}
