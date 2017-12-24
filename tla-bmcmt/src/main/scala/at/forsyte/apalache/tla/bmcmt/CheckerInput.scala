package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * Input to checker. We assume that this input is prepared by AssignmentPass.
  *
  * @param initTransitions a list of transitions that compute the initial states.
  *                        A list [A_1, ..., A_n] is treated as A_1 \/ ... \/ A_n.
  *                        In contrast to Init in TLA+, we require the disjuncts {A_i} to contain only primed variables.
  *                        Each disjunct should assign a value to every primed variable at least once (see assignmentSolver).
  *
  * @param nextTransitions a list of transitions that compute the next states.
  *                        A list [A_1, ..., A_n] is treated as A_1 \/ ... \/ A_n.
  *                        Each disjunct should assign a value to every primed variable at least once (see assignmentSolver).
  *
  * @param invariant       an optional invariant to check. If no invariant is provided, then the checker should only
  *                        test the system for deadlocks.
  *
  * @author Igor Konnov
  */
class CheckerInput(val initTransitions: List[TlaEx],
                   val nextTransitions: List[TlaEx],
                   val invariant: Option[TlaEx]) {
}
