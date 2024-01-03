package at.forsyte.apalache.tla.passes.assignments

import at.forsyte.apalache.tla.passes.imp.PassWithOutputs

/**
 * This pass finds symbolic transitions in a TLA+ specification.
 */
trait TransitionPass extends PassWithOutputs
