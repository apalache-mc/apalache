package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.ConstT
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell}
import at.forsyte.apalache.tla.lir.convenience.tla

/**
  * A cache for string constants that are translated as uninterpreted constants in SMT.
  * Since two TLA+ strings are equal iff they are literally the same string, we force
  * inequality between all the respective SMT constants.
  *
  * @author Igor Konnov
  */
class StrValueCache(solverContext: SolverContext)
    extends AbstractCache[Arena, String, ArenaCell]
    with Serializable {

  override protected def create(
      arena: Arena,
      strValue: String
  ): (Arena, ArenaCell) = {
    // introduce a new cell
    val newArena = arena.appendCell(ConstT())
    val newCell = newArena.topCell
    // the freshly created cell should differ from the others
    for (other <- values()) {
      solverContext.assertGroundExpr(tla.neql(newCell.toNameEx, other.toNameEx))
    }
    solverContext.log("; cached \"%s\" to %s".format(strValue, newCell))
    (newArena, newCell)
  }
}
