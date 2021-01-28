package at.forsyte.apalache.tla.bmcmt.rewriter

/**
  * An object implementing Recoverable implements two methods: snapshot and recover. The method 'snapshot' takes
  * a snapshot of the object state. This snapshot can be restored with the method 'recover'.
  */
trait Recoverable[T] {

  /**
    * Take a snapshot and return it
    * @return the snapshot
    */
  def snapshot(): T

  /**
    * Recover a previously saved snapshot (not necessarily saved by this object).
    * @param shot a snapshot
    */
  def recover(shot: T): Unit
}
