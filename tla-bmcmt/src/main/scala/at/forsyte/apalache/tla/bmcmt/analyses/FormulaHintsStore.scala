package at.forsyte.apalache.tla.bmcmt.analyses
import at.forsyte.apalache.tla.bmcmt.analyses.FormulaHintsStore.FormulaHint
import at.forsyte.apalache.tla.lir.UID

/**
  * A store for formula hints.
  */
trait FormulaHintsStore {
  def getHint(uid: UID): Option[FormulaHint]
}

object FormulaHintsStore {
  abstract class FormulaHint

  /**
    * Hint about a conjunction that is located only under other conjunctions and quantifiers.
    */
  case class HighAnd() extends FormulaHint
}
