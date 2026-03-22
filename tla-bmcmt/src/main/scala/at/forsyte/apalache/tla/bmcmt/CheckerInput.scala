package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule, TlaOperDecl}

/**
 * Input to ModelChecker. We assume that this input is prepared by TransitionPass.
 *
 * @param rootModule
 *   a TLA+ module
 * @param initTransitions
 *   a list of transitions that compute the initial states. A list [A_1, ..., A_n] is treated as A_1 \/ ... \/ A_n. In
 *   contrast to Init in TLA+, we require the disjuncts {A_i} to contain only primed variables. Each disjunct should
 *   assign a value to every primed variable at least once (see assignmentSolver).
 * @param nextTransitions
 *   a list of transitions that compute the next states. A list [A_1, ..., A_n] is treated as A_1 \/ ... \/ A_n. Each
 *   disjunct should assign a value to every primed variable at least once (see assignmentSolver).
 * @param constInitPrimed
 *   An optional initializer of CONSTANTS (over their primed versions).
 * @param verificationConditions
 *   Verification conditions (invariants).
 * @param persistentDecls
 *   A map of operator names to their declarations.
 * @author
 *   Igor Konnov
 */
class CheckerInput(
    val rootModule: TlaModule,
    val initTransitions: List[TlaEx],
    val nextTransitions: List[TlaEx],
    val constInitPrimed: Option[TlaEx],
    val verificationConditions: CheckerInputVC,
    val persistentDecls: Map[String, TlaOperDecl] = Map.empty) {}
