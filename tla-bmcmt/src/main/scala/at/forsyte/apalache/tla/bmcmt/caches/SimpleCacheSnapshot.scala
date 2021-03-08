package at.forsyte.apalache.tla.bmcmt.caches

import scala.collection.immutable.HashMap

/**
 * A snapshot of SimpleCache that can be recovered into a new SimpleCache.
 * All intermediate context are squashed into a single context.
 *
 * @author Igor Konnov
 */
class SimpleCacheSnapshot[KeyT, ValueT](val cache: Map[KeyT, (ValueT, Int)] = HashMap()) {}
