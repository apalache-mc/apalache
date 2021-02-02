package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
 * A pass that does TLA+ desugaring.
 *
 * @author Igor Konnov
 */
trait DesugarerPass extends Pass with TlaModuleMixin
