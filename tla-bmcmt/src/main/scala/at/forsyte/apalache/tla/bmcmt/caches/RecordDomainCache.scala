package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.arena.{ElemPtr, PureArenaAdapter, SmtConstElemPtr}
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.{SetT1, StrT1}
import at.forsyte.apalache.tla.types.tla

import scala.collection.immutable.SortedSet

/**
 * Since we have to create record domains many times, we cache them here.
 *
 * @author
 *   Igor Konnov
 */
class RecordDomainCache(solverContext: SolverContext, strValueCache: ModelValueCache)
    extends AbstractCache[PureArenaAdapter, (SortedSet[String], SortedSet[String]), ArenaCell] with Serializable {

  /**
   * Create a set for a sorted set of record keys.
   *
   * @param context
   *   the context before creating a new value
   * @param usedAndUnusedKeys
   *   two sets: the keys in the domain and the keys outside of the domain
   * @return
   *   a target value that is going to be cached and the new context
   */
  override def create(
      context: PureArenaAdapter,
      usedAndUnusedKeys: (SortedSet[String], SortedSet[String])): (PureArenaAdapter, ArenaCell) = {
    val usedKeys = usedAndUnusedKeys._1
    val unusedKeys = usedAndUnusedKeys._2
    val allKeys: SortedSet[String] = usedKeys.union(unusedKeys)
    var arena = context

    def strToCell(str: String): ElemPtr = {
      val (newArena, cell) = strValueCache.getOrCreate(arena, (StrT1.toString, str))
      arena = newArena
      SmtConstElemPtr(cell)
    }

    val allCells = allKeys.toList.map(strToCell)
    // create the domain cell
    arena = arena.appendCell(SetT1(StrT1))
    val set = arena.topCell
    arena = arena.appendHas(set, allCells: _*)
    // force that every key in the usedKeys is in the set, whereas every key in the unusedKeys is outside of the set
    for ((cell, key) <- allCells.zip(allKeys)) {
      val cond =
        if (usedKeys.contains(key)) {
          tla.storeInSet(cell.elem.toBuilder, set.toBuilder)
        } else {
          tla.not(tla.selectInSet(cell.elem.toBuilder, set.toBuilder))
        }

      solverContext.assertGroundExpr(cond)
    }
    (arena, set)
  }
}
