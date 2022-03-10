package at.forsyte.apalache.tla.bmcmt.caches

import at.forsyte.apalache.tla.bmcmt.rules.aux.DefaultValueFactory
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaType1

/**
 * A cache for default values that are created via DefaultValueFactory.
 *
 * @author
 *   Igor Konnov
 */
class DefaultValueCache(rewriter: SymbStateRewriter)
    extends AbstractCache[SymbState, TlaType1, ArenaCell] with Serializable {
  private val factory = new DefaultValueFactory(rewriter)

  override protected def create(state: SymbState, typ: TlaType1): (SymbState, ArenaCell) = {
    val nextState = factory.makeUpValue(state, CellT.fromType1(typ))
    (nextState, nextState.asCell)
  }
}
