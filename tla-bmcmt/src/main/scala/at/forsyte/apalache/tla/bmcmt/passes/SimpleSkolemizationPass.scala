package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.Pass
import at.forsyte.apalache.tla.assignments.passes.SpecWithTransitionsMixin

/**
  * A pass that runs simple skolemization.
  *
  * @author Igor Konnov
  */
trait SimpleSkolemizationPass extends Pass with SpecWithTransitionsMixin
