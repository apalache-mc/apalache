package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.UID

/**
 * An equivalence class that keeps track of type variables that are considered equal, e.g.,
 * by unification or constraint solving.
 *
 * @param includedVars a non-empty set of variables
 * @author Igor Konnov
 */
class EqClass(includedVars: Set[Int]) {
  require(includedVars.nonEmpty)

  /**
   * A unique identifier of the equivalence class.
   */
  val uid: UID = UID.unique

  /**
   * Type variables that are associated with the equivalence class.
   */
  private var _typeVars: Set[Int] = includedVars

  /**
   * The representative of an equivalence class.
   */
  private var _reprVar: Int = includedVars.reduce(Math.min)

  /**
   * Get the representative variable of a class.
   *
   * @return a fixed variable from the class that works as a class representative.
   */
  def reprVar: Int = _reprVar

  /**
   * Get the type variables that are associated with the equivalence class.
   */
  def typeVars: Set[Int] = _typeVars

  /**
   * Set the type variables that are associated with the equivalence class.
   *
   * @param newSet the new set
   */
  def typeVars_=(newSet: Set[Int]): Unit = {
    require(newSet.nonEmpty)
    _typeVars = newSet
    _reprVar = newSet.reduce(Math.min)
  }

  /**
   * Introduce a fresh copy of the equivalence class that has a different identifier.
   *
   * @return a fresh copy of the class
   */
  def copy(): EqClass = {
    EqClass(this._typeVars)
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
    _typeVars == other._typeVars
  }
}

object EqClass {
  def apply(oneVar: Int): EqClass = {
    apply(Set(oneVar))
  }

  def apply(newVars: Set[Int]): EqClass = {
    new EqClass(newVars)
  }
}
