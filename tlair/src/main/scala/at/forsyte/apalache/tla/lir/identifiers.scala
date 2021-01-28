package at.forsyte.apalache.tla.lir

import java.util.concurrent.atomic.AtomicLong

/**
  * This is a basic class for keeping expression identifiers. The most important feature is the method unique
  * in the companion object, which allows us to assign unique identifiers to different expressions.
  *
  * @param id the value of the identifier.
  */
class UID protected (val id: Long) extends Serializable {

  override def hashCode(): Int = id.hashCode()

  def canEqual(other: Any): Boolean = other.isInstanceOf[UID]

  override def equals(other: Any): Boolean = other match {
    case that: UID =>
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
      throw new IllegalStateException(
        "Too many identifiers, change the underlying representation of UID."
      )
    }
    new UID(newId)
  }
}

trait Identifiable extends Ordered[Identifiable] {
  val ID: UID = UID.unique

  override def compare(that: Identifiable): Int = ID.id.compareTo(that.ID.id)
}
