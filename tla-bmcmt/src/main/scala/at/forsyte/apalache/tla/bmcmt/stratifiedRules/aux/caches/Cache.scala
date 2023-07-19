package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.caches

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.DelayedConstraintGenerator

import scala.collection.immutable.HashMap

/**
 * Creates a stack-like bidirectional cache, which behaves in the following way: Suppose there exists a deterministic
 * injective function `f: (ContextT, SourceT) -> (ContextT, TargetT)`, that is, a function which, given a value of type
 * `SourceT`, computes a value of type `TargetT`, while mutating a context of type `ContextT`.
 *
 * [[Cache]] defines an entry-point `getOrCreate`, such that
 *   - `getOrCreate(c, x) = f(c,x)`, if this is the first time `x` appears as the source value for `getOrCreate`.
 *   - `getOrCreate(c, x) = (c, v)`, if `getOrCreate(c', x)` was previously called, and returned `(c'', v)` (for some
 *     `c', c''`).
 *
 * Concretely, `create` defines the behavior of `f`.
 *
 * The state of the cache can be saved by `push` and later restored by `pop`, similar to an SMT context.
 *
 * Example: IntValueCache assigns [[ArenaCell]]s to Ints, while modifying a [[PureArena]]. Here, `f(a: PureArena, x:
 * Int): (PureArena, ArenaCell) = (a', v)`, where `a' = a.appendCell(CellTFrom(IntT1))` and `v` is the fresh cell added
 * via `appendCell`.
 *
 * @author
 *   Jure Kukovec
 */
abstract class Cache[ContextT, SourceT, TargetT] extends DelayedConstraintGenerator[(SourceT, TargetT)] {
  type LevelT = Int

  /** The "stack" level */
  private var _level: LevelT = 0

  // the base map, tracking the level at which each entry was added.
  private var _cache: Map[SourceT, (TargetT, LevelT)] = HashMap()
  // inherited classes can read, but not modify without going thorough the public interface methods
  protected def cache: Map[SourceT, (TargetT, LevelT)] = _cache

  // reverse mapping
  private var _reverseCache: Map[TargetT, (SourceT, LevelT)] = HashMap()
  // inherited classes can read, but not modify without going thorough the public interface methods
  protected def reverseCache: Map[TargetT, (SourceT, LevelT)] = _reverseCache

  def values(): Iterable[TargetT] = reverseCache.keys

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
   * If this is the first time this method is called with `srcValue`, then it calls `create`, then caches and returns
   * the outcome. Otherwise, it returns the previously cached value.
   *
   * @param context
   *   the context in which the cache is called
   * @param srcValue
   *   a source value
   * @return
   *   a new context and target value. If the target value is being read from a preexisting cache entry, the returned
   *   context is exactly `context`.
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
  private def addToCache(source: SourceT, target: TargetT): Unit = {
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

  // Stack-like behavior

  /**
   * Get the current level, that is the difference between the number of pushes and pops made so far.
   *
   * @return
   *   the current level, always non-negative.
   */
  def level: Int = _level

  /**
   * Save the current state and push it on the stack for a later recovery with pop. Increases level by 1.
   */
  def push(): Unit = _level += 1

  /**
   * Discard all entries added at the current level. Decreases level by 1.
   *
   * Importantly, pop may be called multiple times and thus it is not sufficient to save only the latest state.
   */
  def pop(): Unit = pop(1)

  /**
   * Pop n times.
   * @param n
   *   pop n times, if n > 0, otherwise, do nothing
   */
  def pop(n: Int): Unit = {
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
  def dispose(): Unit = {
    _cache = HashMap.empty
    _reverseCache = HashMap.empty
    _level = 0
  }

  // Partial implementation of DelayedConstraintGenerator

  /**
   * We assume that cache reverts are synced with arena and smt context reverts. Therefore, "all constraints" in the
   * [[DelayedConstraintGenerator]] sense, refers to constraints for all elements _at the current level_.
   */
  def addAllConstraints(ctx: SolverContext): Unit =
    cache.withFilter { _._2._2 == level }.foreach { case (key, (value, _)) =>
      addConstraintsForElem(ctx)(key, value)
    }
}
