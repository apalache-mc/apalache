package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.StackableContext
import at.forsyte.apalache.tla.bmcmt.rewriter.Recoverable

import scala.collection.immutable.HashMap

/**
  * An abstract cache that implements StackableContext.
  *
  * @author Igor Konnov
  */
abstract class AbstractCache[ContextT, SourceT, TargetT]
    extends StackableContext with Serializable with Recoverable[AbstractCacheSnapshot[ContextT, SourceT, TargetT]] {

  /**
    * A context level, see StackableContext
    */
  private var level: Int = 0

  // cache the integer constants that are introduced in SMT for integer literals
  private var cache: Map[SourceT, (TargetT, Int)] = HashMap()
  // reverse mapping
  private var reverseCache: Map[TargetT, (SourceT, Int)] = Map()

  def values(): Iterable[TargetT] = {
    cache.values.map(_._1)
  }

  /**
    * Create a target value based on the source value and cache it.
    *
    * @param context the context before creating a new value
    * @param srcValue a source value
    * @return a target value that is going to be cached and the new context
    */
  protected def create(context: ContextT, srcValue: SourceT): (ContextT, TargetT)

  /**
    * Get a previously cached value for a given source value, or return the previously cached one.
    * Whenever a new value is created, it is cached. The cached value can be later removed by pop.
    *
    * @param srcValue a source value
    * @return a target value
    */
  def getOrCreate(context: ContextT, srcValue: SourceT): (ContextT, TargetT) = {
    if (cache.contains(srcValue)) {
      (context, cache(srcValue)._1)
    } else {
      // introduce a new constant
      val (newContext, targetValue) = create(context, srcValue)
      cache = cache + (srcValue -> (targetValue, level))
      reverseCache = reverseCache + (targetValue -> (srcValue, level))
      (newContext, targetValue)
    }
  }

  /**
    * Get a previously cached value for a given source value, if there is one. Otherwise, return none.
    * @param srcValue a source value
    * @return Some(result), or None
    */
  def get(srcValue: SourceT): Option[TargetT] = {
    cache.get(srcValue) match {
      case Some((target, _)) => Some(target)
      case None => None
    }
  }

  /**
    * Find the key that was used to create a given value.
    * @param value a value, for which the key should be found
    * @return the key, if exists
    */
  def findKey(value: TargetT): Option[SourceT] = {
    reverseCache.get(value) match {
      case Some((key, _)) => Some(key)
      case None => None
    }
  }

  /**
    * Take a snapshot and return it
    *
    * @return the snapshot
    */
  override def snapshot(): AbstractCacheSnapshot[ContextT, SourceT, TargetT] = {
    val squashedCache = cache.map { case (source, (target, _)) => (source, (target, 0)) }
    val squashedRevCache = reverseCache.map { case (target, (source, _)) => (target, (source, 0)) }
    new AbstractCacheSnapshot(squashedCache, squashedRevCache)
  }

  /**
    * Recover a previously saved snapshot (not necessarily saved by this object).
    *
    * @param shot a snapshot
    */
  override def recover(shot: AbstractCacheSnapshot[ContextT, SourceT, TargetT]): Unit = {
    cache = shot.cache
    reverseCache = shot.reverseCache
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

    def isEntryOld(mapEntry: (SourceT, (TargetT, Int))): Boolean =
      mapEntry._2._2 <= level

    def isRevEntryOld(mapEntry: (TargetT, (SourceT, Int))): Boolean =
      mapEntry._2._2 <= level

    cache = cache filter isEntryOld
    reverseCache = reverseCache filter isRevEntryOld
  }

  /**
    * Clean the context.
    */
  override def dispose(): Unit = {
    cache = Map()
    reverseCache = Map()
    level = 0
  }
}
