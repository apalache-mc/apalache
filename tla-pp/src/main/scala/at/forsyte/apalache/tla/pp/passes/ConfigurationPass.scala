package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
  * The pass that collects the configuration parameters and overrides constants and definitions.
  *
  * @author Igor Konnov
  */
trait ConfigurationPass extends Pass with TlaModuleMixin
