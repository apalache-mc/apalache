package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, SolverContext}
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{OperEx, ValEx}

/**
  * A cache for integer constants that maps an integer to an integer constant in SMT.
  *
  * @author Igor Konnov
  */
class IntValueCache(solverContext: SolverContext) extends AbstractCache[Arena, Int, ArenaCell] with Serializable {

  def create(arena: Arena, intValue: Int): (Arena, ArenaCell) = {
    // introduce a new constant
    val newArena = arena.appendCell(IntT())
    val intCell = newArena.topCell
    solverContext.assertGroundExpr(OperEx(TlaOper.eq, intCell.toNameEx, ValEx(TlaInt(intValue))))
    (newArena, intCell)
  }
}
