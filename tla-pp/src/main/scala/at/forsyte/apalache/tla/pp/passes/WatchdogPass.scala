package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
 * The pass that rejects input, if it falls outside of a supported fragment.
 */
trait WatchdogPass extends Pass with TlaModuleMixin
