package at.forsyte.apalache.tla.bmcmt

package object types {
  /**
    * A simple type system for the symbolic memory cells.
    */
  sealed abstract class CellType {
    /**
      * Test whether two types may produce objects that are comparable.
      *
      * @param other other type
      * @return true, if objects of the given types may be comparable
      */
    def comparableWith(other: CellType): Boolean = {
      (this, other) match {
        case (UnknownType(), _) =>
          true

        case (_, UnknownType()) =>
          true

        case (BoolType(), BoolType()) =>
          true

        case (FinSetType(left), FinSetType(right)) =>
          left.comparableWith(right)

        case (FunType(leftDom, leftCodom), FunType(rightDom, rightCodom)) =>
          leftDom.comparableWith(rightDom) && leftCodom.comparableWith(rightCodom)

        case _ =>
          false
      }
    }
  }

  /**
    * An unknown variable, or a type variable.
    */
  case class UnknownType() extends CellType {
  }

  /**
    * A Boolean cell type.
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
