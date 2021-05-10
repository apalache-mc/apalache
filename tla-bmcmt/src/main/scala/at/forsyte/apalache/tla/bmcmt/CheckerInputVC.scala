package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * Verification conditions that have to be checked by the model checker.
 *
 * @param stateInvariantsAndNegations  a list of state invariants and their negations
 * @param actionInvariantsAndNegations a list of action invariants and their negations
 * @param traceInvariantsAndNegations  a list of trace invariants and their negations
 * @author Igor Konnov
 */
case class CheckerInputVC(stateInvariantsAndNegations: List[(TlaEx, TlaEx)] = List(),
    actionInvariantsAndNegations: List[(TlaEx, TlaEx)] = List(),
    traceInvariantsAndNegations: List[(TlaEx, TlaEx)] = List()) {}
