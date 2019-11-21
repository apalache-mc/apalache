package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
  * The pass that generates verification conditions.
  *
  * @author Igor Konnov
  */
trait VCGenPass extends Pass with TlaModuleMixin
