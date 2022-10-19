package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.tla.imp.passes.PassWithOutputs

/**
 * A pass that does all pre-processing of TLA+ code before the assignment solver and the model checker can be run.
 *
 * @author
 *   Igor Konnov
 */
trait PreproPass extends PassWithOutputs
