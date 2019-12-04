package at.forsyte.apalache.tla.types.passes

import at.forsyte.apalache.infra.passes.{Pass, TlaModuleMixin}

/**
  * A pass that produces type annotations.
  *
  * @author Igor Konnov
  */
trait TypeAnnotationPass extends Pass with TlaModuleMixin
