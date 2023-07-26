package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, PureArena}
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.types.tla

/**
 * A cache for integer constants that maps an integer to an integer constant in SMT.
 *
 * @author
 *   Jure Kukovec
 */
class IntValueCache extends Cache[PureArena, BigInt, ArenaCell] {

  protected def create(arena: PureArena, intValue: BigInt): (PureArena, ArenaCell) = {
    // introduce a new constant
    val newArena = arena.appendCell(CellT.fromType1(IntT1))
    val intCell = newArena.topCell
    (newArena, intCell)
  }

  /** The IntValueCache maintains that a cell cache for an integer N is equal to N in SMT. */
  override def addConstraintsForElem(ctx: SolverContext): ((BigInt, ArenaCell)) => Unit = { case (k, v) =>
    ctx.assertGroundExpr(tla.eql(v.toBuilder, tla.int(k)))
  }

}
