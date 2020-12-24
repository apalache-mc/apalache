package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
  * The interface for the ETC type checker.
  */
trait EtcTypeCheckerPass extends Pass with TlaModuleMixin
