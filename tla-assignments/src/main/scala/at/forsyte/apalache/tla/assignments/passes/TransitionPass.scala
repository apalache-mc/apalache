package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.tla.imp.passes.PassWithOutputs

/**
 * This pass finds symbolic transitions in a TLA+ specification.
 */
trait TransitionPass extends PassWithOutputs
