package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.{SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * An abstract version of an oracle that is used e.g. in CherryPick.
  *
  * @author Igor Konnov
  */
trait Oracle {
  /**
    * Produce an expression that states that the oracle values equals to the given integer position.
    * The actual implementation may be different from an integer comparison.
    *
    * @param state a symbolic state
    * @param position a position the oracle should be equal to
    */
  def oracleEqTo(state: SymbState, position: Int): TlaEx

}
