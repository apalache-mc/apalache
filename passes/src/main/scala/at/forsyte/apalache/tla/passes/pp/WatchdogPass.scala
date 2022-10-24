package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.infra.passes.Pass

/**
 * The pass that rejects input, if it falls outside of a supported fragment.
 */
trait WatchdogPass extends Pass
