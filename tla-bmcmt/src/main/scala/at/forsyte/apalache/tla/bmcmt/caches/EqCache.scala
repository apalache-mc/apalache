package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.caches.EqCache._
import at.forsyte.apalache.tla.bmcmt.rewriter.Recoverable
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, StackableContext}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla

import scala.collection.mutable

object EqCache {
  sealed abstract class CacheEntry

  case class FalseEntry() extends CacheEntry

  case class TrueEntry() extends CacheEntry

  case class EqEntry() extends CacheEntry

  case class ExprEntry(ex: TlaEx) extends CacheEntry
}

/**
  * Equality cache.
  *
  * @author Igor Konnov
  */
class EqCache()
    extends StackableContext
    with Serializable
    with Recoverable[EqCacheSnapshot] {

  /**
    * The current context level, see StackableContext.
    */
  private var level: Int = 0

  /**
    * A set of pairs, for which the equality constraints have been generated in SMT.
    * This set can be partially cleaned up, when the pop method is called.
    *
    * The cache invariant key (left, right) is maintained: left.id <= right.id
    */
  private var eqCache: mutable.Map[(ArenaCell, ArenaCell), (CacheEntry, Int)] =
    new mutable.HashMap[(ArenaCell, ArenaCell), (CacheEntry, Int)]()

  def put(left: ArenaCell, right: ArenaCell, entry: CacheEntry): Unit = {
    if (left.id <= right.id) {
      eqCache.put((left, right), (entry, level))
    } else {
      eqCache.put((right, left), (entry, level))
    }
  }

  def get(left: ArenaCell, right: ArenaCell): Option[CacheEntry] = {
    if (left.id <= right.id) {
      val result = eqCache.get((left, right))
      if (result.isDefined) Some(result.get._1) else None
    } else {
      val result = eqCache.get((right, left))
      if (result.isDefined) Some(result.get._1) else None
    }
  }

  def toTla(left: ArenaCell, right: ArenaCell, cacheResult: CacheEntry): TlaEx =
    cacheResult match {
      case FalseEntry() =>
        tla.bool(false)

      case TrueEntry() =>
        tla.bool(true)

      case EqEntry() =>
        tla.eql(left.toNameEx, right.toNameEx)

      case ExprEntry(ex) =>
        ex
    }

  /**
    * Get an immutable copy of the map
    * @return the immutable copy of the cache entries
    */
  def getMap: Map[(ArenaCell, ArenaCell), (CacheEntry, Int)] = eqCache.toMap

  /**
    * Take a snapshot and return it
    *
    * @return the snapshot
    */
  override def snapshot(): EqCacheSnapshot = {
    val squashedCache = eqCache.map {
      case (key, (value, _)) => (key, (value, 0))
    }
    new EqCacheSnapshot(squashedCache)
  }

  /**
    * Recover a previously saved snapshot (not necessarily saved by this object).
    *
    * @param shot a snapshot
    */
  override def recover(shot: EqCacheSnapshot): Unit = {
    eqCache = shot.cache
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
    eqCache.retain((_, value) => value._2 <= level)
  }

  /**
    * Clean the context.
    */
  override def dispose(): Unit = {
    eqCache.clear()
    level = 0
  }
}
