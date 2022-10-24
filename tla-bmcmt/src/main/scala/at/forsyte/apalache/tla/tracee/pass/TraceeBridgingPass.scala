package at.forsyte.apalache.tla.tracee.pass

import at.forsyte.apalache.infra.passes.Pass

/**
 * Bridging pass before BMC, to tie up any configuration that would have been set by passes not utilized in trace
 * evaluation.
 *
 * @author
 *   Jure Kukovec
 */
trait TraceeBridgingPass extends Pass
