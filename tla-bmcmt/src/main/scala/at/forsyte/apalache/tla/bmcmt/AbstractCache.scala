package at.forsyte.apalache.tla.bmcmt

/**
  * An abstract cache that implements StackableContext.
  *
  * @author Igor Konnov
  */
abstract class AbstractCache[ContextT, SourceT, TargetT] extends StackableContext {
  /**
    * A context level, see StackableContext
    */
  private var level: Int = 0

  // cache the integer constants that are introduced in SMT for integer literals
  private var cache: Map[SourceT, (TargetT, Int)] = Map[SourceT, (TargetT, Int)]()

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
  def create(context: ContextT, srcValue: SourceT): (ContextT, TargetT)

  /**
    * Get a previously cache value for a given source value, or return the previously cached one.
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
      (newContext, targetValue)
    }
  }

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
    assert(level > 0)

    def isEntryOlder(mapEntry: (SourceT, (TargetT, Int))): Boolean =
      mapEntry._2._2 < level

    cache = cache filter isEntryOlder
    level -= 1
  }

  /**
    * Pop the context as many times as needed to reach a given level.
    *
    * @param n the number of times to call pop
    */
  override def pop(n: Int): Unit = {
    for (_ <- 1.to(n)) {
      pop()
    }
  }

  /**
    * Clean the context.
    */
  override def dispose(): Unit = {
    cache = Map()
    level = 0
  }
}
