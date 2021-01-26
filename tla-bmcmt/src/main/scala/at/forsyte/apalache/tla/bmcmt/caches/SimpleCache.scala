package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.StackableContext
import at.forsyte.apalache.tla.bmcmt.rewriter.Recoverable

import scala.collection.immutable.HashMap

/**
  * A stackable cache that allows one to store values and retrieve them later.
  *
  * @author Igor Konnov
  */
class SimpleCache[KeyT, ValueT]
    extends StackableContext
    with Recoverable[SimpleCacheSnapshot[KeyT, ValueT]] {

  /**
    * A context level, see StackableContext
    */
  protected var level: Int = 0

  // cache values
  protected var cache: Map[KeyT, (ValueT, Int)] = HashMap()

  def values(): Iterable[ValueT] = {
    cache.map(_._2._1)
  }

  /**
    * Put a value into the cache.
    *
    * @param key   a key
    * @param value a value
    */
  def put(key: KeyT, value: ValueT): Unit = {
    cache += (key -> (value, level))
  }

  /**
    * Get a previously cached value for a given source value, if there is one. Otherwise, return none.
    *
    * @param key a key
    * @return Some(value) if there is a value matching the key, or None otherwise
    */
  def get(key: KeyT): Option[ValueT] = {
    cache.get(key) match {
      case Some((target, _)) => Some(target)
      case None              => None
    }
  }

  /**
    * Take a snapshot and return it
    *
    * @return the snapshot
    */
  override def snapshot(): SimpleCacheSnapshot[KeyT, ValueT] = {
    val squashedCache = cache.map {
      case (key, (value, _)) => (key, (value, 0))
    }
    new SimpleCacheSnapshot(squashedCache)
  }

  /**
    * Recover a previously saved snapshot (not necessarily saved by this object).
    *
    * @param shot a snapshot
    */
  override def recover(shot: SimpleCacheSnapshot[KeyT, ValueT]): Unit = {
    cache = shot.cache
  }

  /**
    * Get the current context level, that is the difference between the number of pushes and pops made so far.
    *
    * @return the current level, always non-negative.
    */
  override def contextLevel: Int = level

  /**
    * Save the current context and push it on the stack for a later recovery with pop.
    */
  override def push(): Unit = {
    level += 1
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    pop(1)
  }

  /**
    * Pop the context as many times as needed to reach a given level.
    *
    * @param n the number of times to call pop
    */
  override def pop(n: Int): Unit = {
    assert(level >= n)
    level -= n

    def isEntryOld(mapEntry: (KeyT, (ValueT, Int))): Boolean =
      mapEntry._2._2 <= level

    cache = cache filter isEntryOld
  }

  /**
    * Clean the context.
    */
  override def dispose(): Unit = {
    cache = Map()
    level = 0
  }
}
