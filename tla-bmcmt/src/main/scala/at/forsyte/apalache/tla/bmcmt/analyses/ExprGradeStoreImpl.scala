package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.UID
import com.google.inject.Singleton

import scala.collection.mutable

@Singleton
class ExprGradeStoreImpl extends ExprGradeStore with Serializable {
  var store: mutable.Map[UID, ExprGrade.Value] = mutable.HashMap[UID, ExprGrade.Value]()

  override def get(uid: UID): Option[ExprGrade.Value] = {
    store.get(uid)
  }
}
