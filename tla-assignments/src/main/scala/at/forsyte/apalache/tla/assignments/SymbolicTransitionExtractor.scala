package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker

/**
  * Performs the complete procedure of finding symbolic transitions from the TLA+ implementation.
  *
  * @see [[AssignmentStrategyEncoder]], [[SMTInterface]], [[SymbTransGenerator]]
  *
  * Jure, 28.8.19: Should symbolic transitions track their origin?
  * Igor, 09.11.19: yes, that is needed for all kinds of error reporting.
  */
class SymbolicTransitionExtractor(tracker: TransformationTracker) {

  /**
    * Find assignments in an action expression and produce symbolic transitions, if possible.
    *
    * @param vars names of the variables on which actionExpr is operating, e.g, the variables defined with VARIABLES
    * @param actionExpr an expression over primed and unprimed variables, e.g., Next or Init
    * @return A collection of symbolic transitions, if they can be extracted; otherwise, return an empty sequence
    *
    */
  def apply(vars: Seq[String], actionExpr: TlaEx): Seq[SymbTrans] = {
    val strategyEncoder = new AssignmentStrategyEncoder()

    /** Generate an smt encoding of the assignment problem to pass to the SMT solver */
    val smtFormula = strategyEncoder.apply(vars.toSet, actionExpr)

    /** Get strategy from the solver */
    val assignmentStrategyOpt =
      new SMTInterface().apply(smtFormula, strategyEncoder.m_varSym)

    assignmentStrategyOpt map { assignmentStrategy =>
      /** produce symbolic transitions */
      new SymbTransGenerator(tracker).apply(actionExpr, assignmentStrategy)
    } getOrElse Seq.empty
  }

}

object SymbolicTransitionExtractor {
  def apply(tracker: TransformationTracker): SymbolicTransitionExtractor = {
    new SymbolicTransitionExtractor(tracker)
  }
}
