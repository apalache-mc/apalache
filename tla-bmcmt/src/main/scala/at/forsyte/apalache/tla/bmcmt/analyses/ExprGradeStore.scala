package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.UID

/**
 * A storage of expression grades.
 *
 * @author Igor Konnov
 */
trait ExprGradeStore {
  def get(uid: UID): Option[ExprGrade.Value]
}
