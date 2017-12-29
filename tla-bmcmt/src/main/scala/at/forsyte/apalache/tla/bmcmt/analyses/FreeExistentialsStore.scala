package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.UID

/**
  * A store that labels free existential expressions,
  * that is, \E x \in S. P that is neither covered by \A, nor by ~.
  *
  * @author Igor Konnov
  */
trait FreeExistentialsStore {
  def isFreeExists(uid: UID): Boolean
}
