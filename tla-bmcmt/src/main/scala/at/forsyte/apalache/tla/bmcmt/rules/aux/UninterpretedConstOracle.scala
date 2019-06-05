package at.forsyte.apalache.tla.bmcmt.rules.aux
import at.forsyte.apalache.tla.bmcmt.caches.StrValueCache
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla

class UninterpretedConstOracle(strValueCache: StrValueCache, oracleCell: ArenaCell) extends Oracle {
  /**
    * Produce an expression that states that the oracle values equals to the given integer position.
    * The actual implementation may be different from an integer comparison.
    *
    * @param state    a symbolic state
    * @param position a position the oracle should be equal to
    */
  override def oracleEqTo(state: SymbState, position: Int): TlaEx = {
    val strVal = strValueCache.get(position.toString)
    assert(strVal.isDefined)
    tla.eql(oracleCell.toNameEx, strVal.get.toNameEx)
  }
}
