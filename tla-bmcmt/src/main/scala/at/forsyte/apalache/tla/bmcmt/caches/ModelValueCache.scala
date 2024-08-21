package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.CellTFrom
import at.forsyte.apalache.tla.lir.{ConstT1, StrT1}
import at.forsyte.apalache.tla.types.{tlaU => tla}

/**
 * A cache for model values that are translated as uninterpreted constants, with a unique sort per uniterpreted type.
 * Since two values are equal iff they are literally the same string, we force inequality between all the respective SMT
 * constants.
 *
 * @author
 *   Jure Kukovec
 */
class ModelValueCache(solverContext: SolverContext)
    extends AbstractCache[PureArenaAdapter, (String, String), ArenaCell] with Serializable {
  override protected def create(
      arena: PureArenaAdapter,
      typeAndIndex: (String, String)): (PureArenaAdapter, ArenaCell) = {
    // introduce a new cell
    val (utype, _) = typeAndIndex
    val cellType = if (utype == StrT1.toString) StrT1 else ConstT1(utype)
    val newArena = arena.appendCell(cellType)
    val newCell = newArena.topCell
    // The fresh cell should differ from the previously created cells.
    // We use the SMT constraint (distinct ...).
    val others = values().withFilter(_.cellType == CellTFrom(cellType)).map(_.toBuilder).toSeq
    solverContext.assertGroundExpr(tla.distinct(newCell.toBuilder +: others: _*))
    solverContext.log("; cached \"%s\" to %s".format(typeAndIndex, newCell))
    (newArena, newCell)
  }

  /**
   * Cache multiple values at once at the current level. This method is more efficient than caching multiple values with
   * [[create]]: It does introduce the SMT constraint `distinct` over `n` values instead of introducing `n` calls to
   * `distinct` with an increasing number of arguments: 1, 2, ..., n.
   *
   * @param arena
   *   the arena to start with
   * @param utype
   *   the name of the uninterpreted type to use
   * @param newValues
   *   the values to cache
   * @return
   *   the new arena and the sequence of cells that represent the cached values
   */
  def createAndCacheMany(
      arena: PureArenaAdapter,
      utype: String,
      newValues: Iterable[String]): (PureArenaAdapter, Seq[ArenaCell]) = {
    var nextArena = arena
    // the cells that exist in the cache
    val oldCells = values().withFilter(_.cellType == CellTFrom(ConstT1(utype))).map(_.toBuilder).toSeq
    // the cells that are already cached go to the left, the new cells go to the right
    val foundOrNewCells = newValues.map { value =>
      get((utype, value)).map(Left(_)).getOrElse {
        nextArena = nextArena.appendCell(ConstT1(utype))
        addToCache((utype, value), nextArena.topCell)
        Right(nextArena.topCell)
      }
    }
    val newCells = foundOrNewCells.collect { case Right(c) => c }
    // require that all new cells and old cells are distinct
    if (newCells.nonEmpty) {
      solverContext.assertGroundExpr(tla.distinct(oldCells ++ newCells.map(_.toBuilder): _*))
    }
    (nextArena, foundOrNewCells.map(_.fold(c => c, c => c)).toSeq)
  }
}
