package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}
import at.forsyte.apalache.tla.assignments.passes.SpecWithTransitionsMixin

/**
  * A bounded model checker that uses the symbolic transitions found by AssignmentPass.
  *
  * @author Igor Konnov
  */
trait BoundedCheckerPass extends Pass with SpecWithTransitionsMixin with TlaModuleMixin
