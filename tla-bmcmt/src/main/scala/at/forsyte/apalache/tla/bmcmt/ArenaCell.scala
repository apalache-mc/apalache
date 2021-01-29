package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.Arena.namePrefix
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

object ArenaCell {
  def isValidName(name: String): Boolean = {
    name.startsWith(namePrefix)
  }

  def idFromName(name: String): Int = {
    if (name.startsWith(namePrefix)) {
      name.substring(namePrefix.length).toInt
    } else {
      throw new IllegalArgumentException("Expected a cell name, found: " + name)
    }
  }
}

/**
 * A symbolic memory cell. Each cell has an identifier (similar to a memory address in a physical computer).
 *
 * @author Igor Konnov
 */
class ArenaCell(val id: Int, val cellType: CellT) extends Comparable[ArenaCell] with Serializable {
  override def toString: String = {
    Arena.namePrefix + id
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
