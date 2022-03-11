package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.rules.aux.DefaultValueFactory
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaType1

/**
 * A cache for default values that are created via DefaultValueFactory.
 *
 * @author
 *   Igor Konnov
 */
class DefaultValueCache(rewriter: SymbStateRewriter)
    extends AbstractCache[Arena, TlaType1, ArenaCell] with Serializable {
  private val factory = new DefaultValueFactory(rewriter)

  override protected def create(arena: Arena, typ: TlaType1): (Arena, ArenaCell) = {
    factory.makeUpValue(arena, typ)
  }
}
