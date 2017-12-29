package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.UID
import com.google.inject.Singleton

import scala.collection.mutable

@Singleton
class FreeExistentialsStoreImpl extends FreeExistentialsStore {
  var store: mutable.Set[UID] = mutable.HashSet[UID]()

  def isFreeExists(uid: UID): Boolean = {
    store.contains(uid)
  }
}
