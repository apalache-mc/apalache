package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.rules.aux.DefaultValueFactory
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaType1

/**
 * A cache for default values that are created via DefaultValueFactory.
 *
 * @author
 *   Igor Konnov
 */
class DefaultValueCache(rewriter: SymbStateRewriter)
    extends AbstractCache[PureArenaAdapter, TlaType1, ArenaCell] with Serializable {
  private val factory = new DefaultValueFactory(rewriter)

  override protected def create(arena: PureArenaAdapter, typ: TlaType1): (PureArenaAdapter, ArenaCell) = {
    factory.makeUpValue(arena, typ)
  }
}
