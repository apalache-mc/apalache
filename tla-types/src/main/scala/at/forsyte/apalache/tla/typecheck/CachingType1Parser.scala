package at.forsyte.apalache.tla.typecheck

import scala.collection.mutable

/**
  * A simple cache that collects parsing results. When the cache size reaches MAX_CACHE_SIZE, the cache is reset.
  * If this class becomes a bottleneck, we should switch to an LRU map, which would require a third-party library.
  *
  * @author Igor Konnov
  */
class CachingType1Parser(impl: Type1Parser, maxCacheSize: Int = CachingType1Parser.MAX_CACHE_SIZE) extends Type1Parser {
  private val cache: mutable.HashMap[String, TlaType1] = new mutable.HashMap()

  /**
    * Parse a type from a string.
    *
    * @param text a string
    * @return a type on success; throws TlcConfigParseError on failure
    */
  override def apply(text: String): TlaType1 = {
    cache.get(text) match {
      case Some(cachedType) =>
        cachedType

      case None =>
        val newParsedType = impl(text)
        if (cache.size >= maxCacheSize) {
          cache.clear()
        }
        cache += text -> newParsedType
        newParsedType
    }
  }
}

object CachingType1Parser {
  /**
    * Default maximum cache size.
    */
  val MAX_CACHE_SIZE = 1024
}