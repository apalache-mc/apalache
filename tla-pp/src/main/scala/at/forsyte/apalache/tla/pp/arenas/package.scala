package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, PureArena}
import at.forsyte.apalache.tla.lir.{TlaType1, UID}
import scalaz.Scalaz._
import scalaz._

/**
 * @author
 *   Jure Kukovec
 */
package object arenas {

  type VariableContext = Map[String, ArenaCell]

  sealed case class ArenaComputationContext(
      arena: PureArena,
      varContext: VariableContext,
      cellCreationMap: Map[UID, Map[VariableContext, ArenaCell]])

  type ArenaComputationInternalState[T] = State[ArenaComputationContext, T]

  type ArenaComputation = ArenaComputationInternalState[ArenaCell]

  def getArena: ArenaComputationInternalState[PureArena] = gets { _.arena }
  def getVarCtx: ArenaComputationInternalState[VariableContext] = gets { _.varContext }

  def bind(name: String, cell: ArenaCell): ArenaComputationInternalState[Unit] = modify[ArenaComputationContext] {
    ctx =>
      ctx.copy(varContext = ctx.varContext + (name -> cell))
  }

  def newCell(uid: UID, cellType: TlaType1): ArenaComputation = State[ArenaComputationContext, ArenaCell] {
    case s @ ArenaComputationContext(arena, varContext, cellCreationMap) =>
      val cellT = CellT.fromType1(cellType)
      val newArena = arena.appendCell(cellT)
      val newCell = newArena.topCell
      val newMap = cellCreationMap + (uid -> (cellCreationMap.getOrElse(uid, Map.empty) + (varContext -> newCell)))
      (s.copy(arena = newArena, cellCreationMap = newMap), newCell)
  }

}
