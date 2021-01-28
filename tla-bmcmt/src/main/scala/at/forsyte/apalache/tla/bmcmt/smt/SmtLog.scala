package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.smt.SmtLog.{AssertGroundExprRecord, DeclareCellRecord, DeclareInPredRecord, Record}
import at.forsyte.apalache.tla.lir.TlaEx

object SmtLog {
  /**
    * A record in the solver log
    */
  sealed abstract class Record extends Serializable

  case class DeclareCellRecord(cell: ArenaCell) extends Record with Serializable
  case class DeclareInPredRecord(set: ArenaCell, elem: ArenaCell) extends Record with Serializable
  case class AssertGroundExprRecord(ex: TlaEx) extends Record with Serializable
}

/**
  * A differential log of declarations and assertions that were submitted to the SMT solver.
  *
  * @author Igor Konnov
  */
class SmtLog(val parentLog: Option[SmtLog], val records: List[SmtLog.Record]) {

  def replay(solver: SolverContext): Unit = {
    def applyRecord: Record => Unit = {
      case DeclareCellRecord(cell) => solver.declareCell(cell)
      case DeclareInPredRecord(set, elem) => solver.declareInPredIfNeeded(set, elem)
      case AssertGroundExprRecord(ex) => solver.assertGroundExpr(ex)
    }

    // replay the parent's log first
    parentLog.foreach(_.replay(solver))
    // then, replay the diff
    records foreach applyRecord
  }

  /**
    * Compute the number of records, including the records in the parent.
    * @return the total number of records, all way up to the root.
    */
  def lengthRec: Int = {
    parentLog match {
      case None => records.length
      case Some(parent) => records.length + parent.lengthRec
    }
  }

}
