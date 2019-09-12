package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
  * A pass that runs simple skolemization.
  *
  * @author Igor Konnov
  */
trait HintsAndSkolemizationPass extends Pass with TlaModuleMixin
