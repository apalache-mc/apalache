package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.Pass
import at.forsyte.apalache.tla.assignments.passes.SpecWithTransitionsMixin

/**
  * Grade the specification subexpressions.
  */
trait GradePass extends Pass with SpecWithTransitionsMixin {
}
