package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.caches.EqCache.CacheEntry

import scala.collection.mutable

/**
  * A snapshot of EqCache that can be recovered into a new EqCache.
  * All intermediate context are squashed into a single context.
  *
  * @author Igor Konnov
  */
class EqCacheSnapshot(val cache: mutable.Map[(ArenaCell, ArenaCell), (CacheEntry, Int)]) {
}
