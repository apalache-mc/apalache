package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
  * This analysis finds formulas of specific structure and labels them with hints.
  * For instance, the top-level conjunctions (that are situated only under other conjunctions and quantifiers)
  * are labelled with a hint.
  *
  * @author Igor Konnov
  */
class HintFinder @Inject()(val hintsStore: FormulaHintsStoreImpl) extends LazyLogging {
  /**
    * Transform the transitions into normal form and label the free existential quantifiers.
    *
    * @param transitions identified transitions
    * @return the modified input
    */
  def findHints(transitions: Seq[TlaEx]): Unit = {
    transitions foreach makeHints
    logger.debug("introduced %d formula hints".format(hintsStore.store.size))
  }


  private def makeHints(ex: TlaEx): Unit = ex match {
    case OperEx(TlaBoolOper.exists, _, _, quantifiedEx) =>
      makeHints(quantifiedEx)

    case OperEx(TlaBoolOper.forall, _, _, quantifiedEx) =>
      makeHints(quantifiedEx)

    case OperEx(TlaBoolOper.and, args@_*) =>
      hintsStore.store.put(ex.ID, FormulaHintsStore.HighAnd())
      args foreach makeHints

    case _ =>
      () // do not explore any further
  }
}
