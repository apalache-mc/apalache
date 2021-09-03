package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.UID

/**
 * An equivalence class that keeps track of type variables that are considered equal, e.g.,
 * by unification or constraint solving.
 *
 * @author Igor Konnov
 */
class EqClass {

  /**
   * A unique identifier of the equivalence class.
   */
  val uid: UID = UID.unique

  /**
   * Type variables that are associated with the equivalence class.
   */
  var typeVars: Set[Int] = Set.empty

  /**
   * Introduce a fresh copy of the equivalence class that has a different identifier.
   *
   * @return a fresh copy of the class
   */
  def copy(): EqClass = {
    EqClass(this.typeVars)
  }

  def canEqual(other: Any): Boolean = other.isInstanceOf[EqClass]

  override def equals(other: Any): Boolean = other match {
    case that: EqClass => uid == that.uid
    case _             => false
  }

  override def hashCode(): Int = {
    uid.hashCode()
  }

  /**
   * Compare the structure of two equivalence classes: that is whether they have the same sets of variables.
   *
   * @param other another equivalence class
   * @return true, if both classes contain the same sets of variables
   */
  def deepEquals(other: EqClass): Boolean = {
    typeVars == other.typeVars
  }
}

object EqClass {
  def apply(oneVar: Int): EqClass = {
    apply(Set(oneVar))
  }

  def apply(typeVars: Set[Int]): EqClass = {
    val cls = new EqClass
    cls.typeVars = typeVars
    cls
  }
}
