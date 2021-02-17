package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
 * This pass finds symbolic transitions in a TLA+ specification.
 */
trait TransitionPass extends Pass with TlaModuleMixin
