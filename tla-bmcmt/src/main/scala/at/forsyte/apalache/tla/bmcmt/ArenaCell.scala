package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

object ArenaCell {
}

/**
  * A symbolic memory cell. Each cell has an identifier (similar to a memory address in a physical computer).
  *
  * @author Igor Konnov
  */
class ArenaCell(val id: Int, val cellType: CellT) extends Comparable[ArenaCell] {
  override def toString: String = {
    "%s%d".format(CellTheory().namePrefix, id)
  }

  def toNameEx: NameEx = {
    NameEx(toString)
  }

  def mkTlaEq(rhs: ArenaCell): TlaEx = {
      OperEx(TlaOper.eq, this.toNameEx, rhs.toNameEx)
  }

  override def compareTo(t: ArenaCell): Int = {
    id.compareTo(t.id)
  }

  override def hashCode(): Int = id.hashCode()

  override def equals(o: scala.Any): Boolean =
    if (!o.isInstanceOf[ArenaCell]) {
      false
    } else {
      id.equals(o.asInstanceOf[ArenaCell].id)
    }
}
