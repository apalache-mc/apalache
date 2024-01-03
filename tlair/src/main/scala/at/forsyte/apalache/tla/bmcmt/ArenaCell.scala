package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.PureArena.namePrefix
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}
import at.forsyte.apalache.tla.typecomp
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.bmcmt.types.CellT

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
 * @param id
 *   Id of the cell
 * @param cellType
 *   Type of the cell
 * @param isUnconstrained
 *   Flag defining if the SMT representation of the cell is unconstrained, default is false.
 * @author
 *   Igor Konnov
 */
class ArenaCell(val id: Int, val cellType: CellT, val isUnconstrained: Boolean = false)
    extends Comparable[ArenaCell] with Serializable {
  override def toString: String = PureArena.namePrefix + id

  def toNameEx: NameEx = toBuilder.build.asInstanceOf[NameEx]

  /**
   * Convert the cell to a builder instruction, so it can be used to build larger IR expressions.
   *
   * @return
   *   a builder instruction that can be used with the typed builder
   */
  def toBuilder: typecomp.TBuilderInstruction = tla.name(toString, cellType.toTlaType1)

  def mkTlaEq(rhs: ArenaCell): TlaEx = tla.eql(this.toBuilder, rhs.toBuilder)

  override def compareTo(t: ArenaCell): Int = id.compareTo(t.id)

  override def hashCode(): Int = id.hashCode()

  override def equals(o: scala.Any): Boolean =
    if (!o.isInstanceOf[ArenaCell]) {
      false
    } else {
      id.equals(o.asInstanceOf[ArenaCell].id)
    }
}
