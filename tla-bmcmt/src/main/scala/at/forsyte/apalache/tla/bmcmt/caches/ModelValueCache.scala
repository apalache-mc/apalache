package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell}
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.ConstT
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.typecheck.ModelValueHandler

/**
 * A cache for model values that are translated as uninterpreted constants, with a unique sort per uniterpreted type.
 * Since two values are equal iff they are literally the same string, we force
 * inequality between all the respective SMT constants.
 *
 * @author Jure Kukovec
 */
class ModelValueCache(solverContext: SolverContext)
    extends AbstractCache[Arena, (String, String), ArenaCell] with Serializable {
  override protected def create(arena: Arena, typeAndIndex: (String, String)): (Arena, ArenaCell) = {
    // introduce a new cell
    val (utype, _) = typeAndIndex
    val newArena = arena.appendCell(ConstT(utype))
    val newCell = newArena.topCell
    // the freshly created cell should differ from the others
    for (
        other <- values().withFilter { v =>
          v.cellType == ConstT(utype) //compare just with same sorted cells
        }
    ) {
      solverContext.assertGroundExpr(OperEx(ApalacheOper.distinct, newCell.toNameEx, other.toNameEx))
    }
    solverContext.log("; cached \"%s\" to %s".format(typeAndIndex, newCell))
    (newArena, newCell)
  }
}
