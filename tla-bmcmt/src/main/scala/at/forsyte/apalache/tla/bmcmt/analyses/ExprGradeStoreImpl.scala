package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.UID
import com.google.inject.Singleton

import scala.collection.mutable

@Singleton
class ExprGradeStoreImpl extends ExprGradeStore with Serializable {
  private val store: mutable.Map[UID, ExprGrade.Value] = mutable.HashMap[UID, ExprGrade.Value]()

  private[analyses] def put(uid: UID, grade: ExprGrade.Value): Unit = {
    store.update(uid, grade)
  }

  override def get(uid: UID): Option[ExprGrade.Value] = {
    store.get(uid)
  }
}
