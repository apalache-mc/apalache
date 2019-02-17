package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.bmcmt.analyses.FormulaHintsStore.FormulaHint
import at.forsyte.apalache.tla.lir.UID
import com.google.inject.Singleton

import scala.collection.mutable

@Singleton
class FormulaHintsStoreImpl extends FormulaHintsStore {
  var store: mutable.Map[UID, FormulaHint] = mutable.HashMap[UID, FormulaHint]()

  override def getHint(uid: UID): Option[FormulaHint] = {
    store.get(uid)
  }
}
