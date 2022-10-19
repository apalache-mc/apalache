package at.forsyte.apalache.tla.passes.assignments

import at.forsyte.apalache.tla.imp.passes.PassWithOutputs

/**
 * PrimingPass adds primes to the variables in state initializers and constant initializers.
 */
trait PrimingPass extends PassWithOutputs
