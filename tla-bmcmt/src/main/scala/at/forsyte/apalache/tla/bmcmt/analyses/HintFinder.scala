package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
  * <p>This analysis finds formulas of specific structure and labels them with hints.
  * For instance, the top-level conjunctions (that are situated only under other conjunctions and quantifiers)
  * are labelled with a hint.</p>
  *
  * <p>This class will be probably removed in the future, as lazy circuiting with an incremental solver gives us
  * a speed-up only on relatively small instances.</p>
  *
  * @author Igor Konnov
  */
class HintFinder @Inject()(val hintsStore: FormulaHintsStoreImpl) extends LazyLogging {
  def introHints(ex: TlaEx): Unit = ex match {
    case OperEx(TlaBoolOper.exists, _, _, quantifiedEx) =>
      introHints(quantifiedEx)

    case OperEx(TlaBoolOper.forall, _, _, quantifiedEx) =>
      introHints(quantifiedEx)

    case OperEx(TlaBoolOper.and, args@_*) =>
      hintsStore.store.put(ex.ID, FormulaHintsStore.HighAnd())
      args foreach introHints

    case _ =>
      () // do not explore any further
  }
}
