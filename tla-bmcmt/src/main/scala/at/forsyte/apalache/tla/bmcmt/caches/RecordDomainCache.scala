package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{ConstT, FinSetT}
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, SolverContext}
import at.forsyte.apalache.tla.lir.convenience.tla

import scala.collection.immutable.SortedSet

/**
  * Since we have to create record domains many times, we cache them here.
  *
  * @author Igor Konnov
  */
class RecordDomainCache(solverContext: SolverContext, strValueCache: StrValueCache)
  extends AbstractCache[Arena, (SortedSet[String], SortedSet[String]), ArenaCell] with Serializable {

  /**
    * Create a set for a sorted set of record keys.
    *
    * @param context           the context before creating a new value
    * @param usedAndUnusedKeys two sets: the keys in the domain and the keys outside of the domain
    * @return a target value that is going to be cached and the new context
    */
  override def create(context: Arena, usedAndUnusedKeys: (SortedSet[String], SortedSet[String])): (Arena, ArenaCell) = {
    val usedKeys = usedAndUnusedKeys._1
    val unusedKeys = usedAndUnusedKeys._2
    val allKeys: SortedSet[String] = usedKeys.union(unusedKeys)
    var arena = context

    def strToCell(str: String): ArenaCell = {
      val (newArena, cell) = strValueCache.getOrCreate(arena, str)
      arena = newArena
      cell
    }

    val allCells = allKeys.toList map strToCell
    // create the domain cell
    arena = arena.appendCell(FinSetT(ConstT()))
    val set = arena.topCell
    arena = arena.appendHas(set, allCells: _*)
    // force that every key in the usedKeys is in the set, whereas every key in the unusedKeys is outside of the set
    for ((cell, key) <- allCells.zip(allKeys)) {
      val cond =
        if (usedKeys.contains(key)) {
          tla.in(cell, set)
        } else {
          tla.not(tla.in(cell, set))
        }

      solverContext.assertGroundExpr(cond)
    }
    (arena, set)
  }
}
