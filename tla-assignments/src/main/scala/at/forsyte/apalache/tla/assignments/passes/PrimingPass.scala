package at.forsyte.apalache.tla.assignments.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
 * PrimingPass adds primes to the variables in state initializers and constant initializers.
 */
trait PrimingPass extends Pass with TlaModuleMixin
