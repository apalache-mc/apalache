package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
  * A pass that expands operators and let-in definitions.
  *
  * @author Igor Konnov
  */
trait InlinePass extends Pass with TlaModuleMixin
