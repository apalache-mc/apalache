package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.Snapshottable

import scala.collection.immutable.HashMap

/**
 * An abstract cache that assigns `TargetT`-typed values to `SourceT` typed values, while potentially modifying a
 * `ContextT`-typed context.
 *
 * Example: IntValueCache assigns [[ArenaCell]]s to integers, while modifying a [[PureArena]].
 *
 * Some caches maintain a certain contract with the SMT solver, that is, they may add constraints to a
 * [[at.forsyte.apalache.tla.bmcmt.smt.SolverContext]] on demand.
 *
 * @author
 *   Jure Kukovec
 */
abstract class Cache[ContextT, SourceT, TargetT] extends Snapshottable {

  /* While it extends Snapshottable, there's no need to implement an actual snapshot/stack data structure. By assigning each
   * cache entry a level, effectively a timestamp for when it was added, we can proxy the state of the stack, by filtering
   * out entries, based on their levels.
   *
   * Caches need snapshot functionality, because reverting SMT contexts should revert arenas as well, thus freeing certain
   * cells. Otherwise, we could end up with a cache pointing to a cell, which does not exist in a post-revert arena.
   */

  type LevelT = Int

  /**
   * A stack level, see [[Snapshottable]]
   */
  private var _level: LevelT = 0

  // the base map, tracking the level at which each entry was added.
  private var _cache: Map[SourceT, (TargetT, LevelT)] = HashMap()
  // inherited classes can read, but not modify without going thorough the public interface methods
  protected def cache: Map[SourceT, (TargetT, LevelT)] = _cache

  // reverse mapping
  private var _reverseCache: Map[TargetT, (SourceT, LevelT)] = HashMap()
  // inherited classes can read, but not modify without going thorough the public interface methods
  protected def reverseCache: Map[TargetT, (SourceT, LevelT)] = _reverseCache

  def values(): Iterable[TargetT] = _cache.values.map(_._1)

  /**
   * Compute a target value and context update, based on the source value, but do not save the result.
   *
   * @param context
   *   the context before creating a new value
   * @param srcValue
   *   a source value
   * @return
   *   a target value that can be cached, and the new context
   */
  protected def create(context: ContextT, srcValue: SourceT): (ContextT, TargetT)

  /**
   * Get a previously cached value for a given source value, or return the previously cached one. Whenever a new value
   * is created, it is cached. The cached value can be later removed by pop.
   *
   * @param srcValue
   *   a source value
   * @return
   *   a target value
   */
  def getOrCreate(context: ContextT, srcValue: SourceT): (ContextT, TargetT) =
    if (_cache.contains(srcValue)) {
      (context, _cache(srcValue)._1)
    } else {
      // introduce a new constant
      val (newContext, targetValue) = create(context, srcValue)
      addToCache(srcValue, targetValue)
      (newContext, targetValue)
    }

  /**
   * Add a value to the cache.
   *
   * @param source
   *   the source value
   * @param target
   *   the cached target value
   */
  protected def addToCache(source: SourceT, target: TargetT): Unit = {
    _cache += source -> (target, level)
    _reverseCache += target -> (source, level)
  }

  /**
   * Get a previously cached value for a given source value, if there is one. Otherwise, return none.
   *
   * @param srcValue
   *   a source value
   * @return
   *   Some(result), or None
   */
  def get(srcValue: SourceT): Option[TargetT] = cache.get(srcValue).map(_._1)

  /**
   * Find the key that was used to create a given value.
   * @param value
   *   a value, for which the key should be found
   * @return
   *   the key, if exists
   */
  def findKey(value: TargetT): Option[SourceT] = reverseCache.get(value).map(_._1)

  /**
   * Get the current level, that is the difference between the number of pushes and pops made so far.
   *
   * @return
   *   the current level, always non-negative.
   */
  override def level: Int = _level

  /**
   * Save the current state and push it on the stack for a later recovery with pop. Increases level by 1.
   */
  override def snapshot(): Unit = _level += 1

  /**
   * Discard all entries added at the current level. Decreases level by 1.
   *
   * Importantly, pop may be called multiple times and thus it is not sufficient to save only the latest state.
   */
  override def revert(): Unit = revert(1)

  /**
   * Pop n times.
   * @param n
   *   pop n times, if n > 0, otherwise, do nothing
   */
  override def revert(n: Int): Unit = {
    require(level >= n, s"Can't pop $n levels from a cache of level $level.")
    _level -= n

    def isRetained[A, B](mapEntry: (A, (B, Int))): Boolean =
      mapEntry._2._2 <= level

    _cache = cache.filter(isRetained)
    _reverseCache = reverseCache.filter(isRetained)
  }

  /**
   * Clean the state completely.
   */
  override def dispose(): Unit = {
    _cache = HashMap.empty
    _reverseCache = HashMap.empty
    _level = 0
  }

  /** SMT constraints */

  /** Extra method, may add constraints for a single key-value pair */
  def addConstraintsForKV(ctx: SolverContext)(k: SourceT, v: TargetT): Unit

  /**
   * Add implementation-specific constraints for all entries added at `lvl` or later.
   */
  def addConstraintsFromLevel(ctx: SolverContext)(lvl: Int): Unit

  /**
   * Add constraints for all entries added at any level.
   */
  def addConstraints(ctx: SolverContext): Unit = addConstraintsFromLevel(ctx)(0)

  /**
   * Add constraints for all entries added at the current level.
   */
  def addConstraintsForCurrentLevel(ctx: SolverContext): Unit = addConstraintsFromLevel(ctx)(level)

}
