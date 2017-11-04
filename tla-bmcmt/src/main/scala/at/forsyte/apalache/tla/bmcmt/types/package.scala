package at.forsyte.apalache.tla.bmcmt

package object types {
  /**
    * A simple type system for the symbolic memory cells.
    */
  sealed abstract class CellT {
    /**
      * Test whether two types may produce objects that are comparable.
      *
      * @param other other type
      * @return true, if objects of the given types may be comparable
      */
    def comparableWith(other: CellT): Boolean = {
      (this, other) match {
        case (UnknownT(), _) =>
          true

        case (_, UnknownT()) =>
          true

        case (BoolT(), BoolT()) =>
          true

        case (IntT(), IntT()) =>
          true

        case (FinSetT(left), FinSetT(right)) =>
          left.comparableWith(right)

        case (FunT(leftDom, leftCodom), FunT(rightDom, rightCodom)) =>
          leftDom.comparableWith(rightDom) && leftCodom.comparableWith(rightCodom)

        case (SumT(leftTypes), right @ _) =>
          leftTypes.exists(_.comparableWith(right))

        case (left @ _, SumT(rightTypes)) =>
          rightTypes.exists(left.comparableWith)

        case _ =>
          false
      }
    }
  }

  /**
    * An unknown variable, or a type variable.
    */
  case class UnknownT() extends CellT

  /**
    * A Boolean cell type.
    */
  case class BoolT() extends CellT

  /**
    * An integer cell type.
    */
  case class IntT() extends CellT

  /**
    * Sum type T1 + ... + Tn.
    */
  case class SumT(components: Seq[CellT]) extends CellT

  /**
    * A finite set.
    *
    * @param elemType the elements type
    */
  case class FinSetT(elemType: CellT) extends CellT

  /**
    * A function type.
    *
    * @param domType   the type of the domain (must be a finite set).
    * @param codomType type of the co-domain (must be a set).
    */
  case class FunT(domType: CellT, codomType: CellT) extends CellT
}
