package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.CellType

object ArenaCell {
  val namePrefix = "$C$"
}

/**
  * A symbolic memory cell. Each cell has an identifier (similar to a memory address in a physical computer).
  *
  * @author Igor Konnov
  */
class ArenaCell(val id: Int, val cellType: CellType) {
  override def toString: String = {
    "%s%d".format(ArenaCell.namePrefix, id)
  }
}
