package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.types.{tlaU => tla}

/**
 * A cache for integer constants that maps an integer to an integer constant in SMT.
 *
 * @author
 *   Igor Konnov
 */
class IntValueCache(solverContext: SolverContext)
    extends AbstractCache[PureArenaAdapter, BigInt, ArenaCell] with Serializable {

  def create(arena: PureArenaAdapter, intValue: BigInt): (PureArenaAdapter, ArenaCell) = {
    // introduce a new constant
    val newArena = arena.appendCell(IntT1)
    val intCell = newArena.topCell
    solverContext.assertGroundExpr(tla.eql(intCell.toBuilder, tla.int(intValue)))
    (newArena, intCell)
  }
}
