package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * A concrete state that has been decoded from an SMT model.
 *
 * @param assignments
 *   variable bindings for all the state variables
 * @param transitionNo
 *   the number of the transition that led to this state
 */
case class DecodedState(assignments: Map[String, TlaEx], transitionNo: Int)

/**
 * A concrete execution that has been decoded from an SMT model.
 *
 * @param path
 *   the sequence of decoded states, from the initial state to the final state
 *
 * @author
 *   Igor Konnov
 */
case class DecodedExecution(path: List[DecodedState])
