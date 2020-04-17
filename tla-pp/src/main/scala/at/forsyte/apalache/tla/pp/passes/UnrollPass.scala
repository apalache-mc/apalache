package at.forsyte.apalache.tla.pp.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
  * The pass that replaces recursive operators and functions with their finite-depth unrollings
  *
  */
trait UnrollPass extends Pass with TlaModuleMixin
