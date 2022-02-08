package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.{TlaEx, TlaOperDecl}

/**
 * Verification conditions that have to be checked by the model checker.
 *
 * @param stateInvariantsAndNegations
 *   a list of state invariants and their negations
 * @param actionInvariantsAndNegations
 *   a list of action invariants and their negations
 * @param traceInvariantsAndNegations
 *   a list of trace invariants and their negations
 * @param stateView
 *   optional state view that is used for enumerating counterexamples
 * @author
 *   Igor Konnov
 */
case class CheckerInputVC(
    stateInvariantsAndNegations: List[(TlaEx, TlaEx)] = List(),
    actionInvariantsAndNegations: List[(TlaEx, TlaEx)] = List(),
    traceInvariantsAndNegations: List[(TlaOperDecl, TlaOperDecl)] = List(),
    stateView: Option[TlaEx] = None) {}
