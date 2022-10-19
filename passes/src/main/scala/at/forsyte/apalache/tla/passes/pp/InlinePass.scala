package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.tla.imp.passes.PassWithOutputs

/**
 * A pass that expands operators and let-in definitions.
 *
 * @author
 *   Igor Konnov
 */
trait InlinePass extends PassWithOutputs
