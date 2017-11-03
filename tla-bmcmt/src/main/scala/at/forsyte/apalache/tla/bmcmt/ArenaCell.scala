package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.CellType
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

object ArenaCell {
}

/**
  * A symbolic memory cell. Each cell has an identifier (similar to a memory address in a physical computer).
  *
  * @author Igor Konnov
  */
class ArenaCell(val id: Int, val cellType: CellType) {
  override def toString: String = {
    "%s%d".format(CellTheory().namePrefix, id)
  }

  def toNameEx: NameEx = {
    NameEx(toString)
  }

  def mkTlaEq(rhs: ArenaCell): TlaEx = {
      OperEx(TlaOper.eq, this.toNameEx, rhs.toNameEx)
  }
}
