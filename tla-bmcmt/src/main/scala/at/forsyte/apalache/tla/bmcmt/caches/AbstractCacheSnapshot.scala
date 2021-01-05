package at.forsyte.apalache.tla.bmcmt.caches

import scala.collection.immutable.HashMap

/**
  * A snapshot of AbstractCache that can be recovered into a new AbstractCache.
  * All intermediate context are squashed into a single context.
  *
  * @author Igor Konnov
  */
class AbstractCacheSnapshot[ContextT, SourceT, TargetT](val cache: Map[SourceT, (TargetT, Int)] = HashMap(),
                                                        val reverseCache: Map[TargetT, (SourceT, Int)]) {

}
