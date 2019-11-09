package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
  * An optimization pass that applies to KerA+.
  *
  * @author Igor Konnov
  */
trait OptPass extends Pass with TlaModuleMixin
