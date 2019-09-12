package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
  * A bounded model checker that uses the symbolic transitions found by AssignmentPass.
  *
  * @author Igor Konnov
  */
trait BoundedCheckerPass extends Pass with TlaModuleMixin
