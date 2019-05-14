package at.forsyte.apalache.tla.lir

import java.util.concurrent.atomic.AtomicLong

// This file collects the declarations that are related to unique identifiers.
// It is currently under refactoring.

/**
  * This is a basic class for keeping expression identifiers. The most important feature is the method unique
  * in the companion object, which allows us to assign unique identifiers to different expressions.
  *
  * @param id the value of the identifier.
  */
class UID protected(val id: Long) {
  /**
    * This method is deprecated since version 0.4. Our ids are always valid.
    *
    * @return always true
    */
  def valid: Boolean = true

  override def hashCode(): Int = id.hashCode()

  def canEqual(other: Any): Boolean = other.isInstanceOf[UID]

  override def equals(other: Any): Boolean = other match {
    case that: UID =>
      (that canEqual this) &&
        id == that.id
    case _ => false
  }

  override def toString: String = id.toString
}

object UID {
  /**
    * The value of the id that will be assigned by the next call to unique(). We start with 1, to omit the default value 0.
    * By using AtomicLong, we make sure that unique() is assigning unique identifiers in the concurrent setting.
    */
  private var nextId: AtomicLong = new AtomicLong(1)

  // TODO: remove this method in the future, as it allows one to work around uniqueness
  def apply(id: Long) = new UID(id)

  /**
    * Create a unique identifier, provided that all identifiers have been created only by calling this method.
    * This method is thread-safe.
    *
    * @return a new unique identifier
    */
  def unique: UID = {
    val newId = nextId.getAndAdd(1)
    if (newId == Long.MaxValue) {
      throw new IllegalStateException("Too many identifiers, change the underlying representation of UID.")
    }
    new UID(newId)
  }
}

/**
  * This class is defined for backward compatibility with the old code that uses EID.
  *
  * TODO: remove it later
  *
  * @param id an identifier
  */
class EID(override val id: Long) extends UID(id) {}

object EID {
  def apply(id: Long) = new EID(id)
}

// TODO: let's clean up this trait (Igor)
trait Identifiable extends Ordered[Identifiable] {
  protected var m_ID: UID = UID.unique

  protected var canSet: Boolean = true

  // TODO: do we need the ability to override the identifier with an arbitrary value?
  def setID(newID: UID): Unit = {
    if (canSet && newID.valid) {
      canSet = false
      m_ID = newID
    }
    else throw new Identifiable.IDReallocationError
  }

  def ID: UID = m_ID

  /**
    * Get an ID, if one has been assigned, and throw IllegalStateException otherwise.
    *
    * TODO: remove it later, as our identifiers are always valid
    *
    * @return a valid ID
    * @throws IllegalStateException when an identifier has not been assigned yet.
    */
  def safeId: UID = {
    if (m_ID.valid) {
      // this condition always holds
      m_ID
    } else {
      throw new IllegalStateException("An expression has not been assigned an ID yet")
    }
  }

  // TODO: what is the point of forgetting the ids?
  def forget(): Unit = {
    m_ID = UID(-1)
    canSet = true
  }

  // TODO: remove it later
  def valid: Boolean = m_ID.valid

  override def compare(that: Identifiable): Int = {
    that match {
      case other: Identifiable =>
        ID.id.compareTo(other.ID.id)

      case _ =>
        throw new RuntimeException("Comparing Identifiable to " + that.getClass)
    }
  }
}

object IdOrdering extends Ordering[Identifiable] {
  override def compare(x: Identifiable, y: Identifiable): Int = x compare y
}

object Identifiable {

  class IDReallocationError extends Exception

}
