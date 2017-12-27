package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule}

/**
  * An output by the assignment solver.
  *
  * @param rootModule      a TLA+ module that is used as a root
  * @param initTransitions a list of transitions that compute the initial states.
  *                        A list [A_1, ..., A_n] is treated as A_1 \/ ... \/ A_n.
  *                        In contrast to Init in TLA+, we require the disjuncts {A_i} to contain only primed variables.
  *                        Each disjunct should assign a value to every primed variable at least once (see assignmentSolver).
  * @param nextTransitions a list of transitions that compute the next states.
  *                        A list [A_1, ..., A_n] is treated as A_1 \/ ... \/ A_n.
  *                        Each disjunct should assign a value to every primed variable at least once (see assignmentSolver).
  * @author Igor Konnov
  */
class SpecWithTransitions(val rootModule: TlaModule,
                          val initTransitions: List[TlaEx],
                          val nextTransitions: List[TlaEx])