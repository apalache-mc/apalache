package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell}
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{OperEx, ValEx}
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * A cache for integer constants that maps an integer to an integer constant in SMT.
 *
 * @author Igor Konnov
 */
class IntValueCache(solverContext: SolverContext) extends AbstractCache[Arena, BigInt, ArenaCell] with Serializable {

  def create(arena: Arena, intValue: BigInt): (Arena, ArenaCell) = {
    // introduce a new constant
    val newArena = arena.appendCell(IntT())
    val intCell = newArena.topCell
    solverContext.assertGroundExpr(OperEx(TlaOper.eq, intCell.toNameEx, ValEx(TlaInt(intValue))))
    (newArena, intCell)
  }
}
