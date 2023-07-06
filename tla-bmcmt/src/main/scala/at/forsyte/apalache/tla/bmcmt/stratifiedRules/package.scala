package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.{TlaType1, TypeTag}

/**
 * @author
 *   Jure Kukovec
 */
package object stratifiedRules {

  type RuleOutput = (RewriterScope, ArenaCell)

  def addCell(arena: PureArena, cellT: CellT): (PureArena, ArenaCell) = {
    val arenaWithNewCell = arena.appendCell(cellT)
    (arenaWithNewCell, arenaWithNewCell.topCell)
  }

  def addCell(arena: PureArena, tt1: TlaType1): (PureArena, ArenaCell) = {
    addCell(arena, CellT.fromType1(tt1))
  }

  def addCell(arena: PureArena, typeTag: TypeTag): (PureArena, ArenaCell) =
    addCell(arena, CellT.fromTypeTag(typeTag))

}
