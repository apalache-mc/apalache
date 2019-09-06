package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}
import at.forsyte.apalache.tla.assignments.passes.SpecWithTransitionsMixin

/**
  * Label the specification subexpressions with grades, which are similar to TLA+ levels:
  * constant, state-level, action-level, etc. See ExprGrade.
  *
  * After the labelling is done, this pass also replaces all action-level disjunctions
  * with TlaBoolOper.orParallel.
  *
  * @author Igor Konnov
  */
trait GradePass extends Pass with SpecWithTransitionsMixin with TlaModuleMixin {
}
