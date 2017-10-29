package at.forsyte.apalache.tla.bmcmt

package object types {
  /**
    * A type system for the symbolic memory cells.
    */
  abstract class CellType

  /**
    * An unknown variable, or a type variable.
    */
  case class UnknownType() extends CellType

  /**
    * A Boolean type.
    */
  case class BoolType() extends CellType

  /**
    * A finite set.
    *
    * @param elemType the elements type
    */
  case class FinSetType(elemType: CellType) extends CellType

  /**
    * A function type.
    *
    * @param domType   the type of the domain (must be a finite set).
    * @param codomType type of the co-domain (must be a set).
    */
  case class FunType(domType: CellType, codomType: CellType) extends CellType
}
