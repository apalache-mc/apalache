package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.tla.lir.TlaModule

/**
  * A pass that receives a TLA+ module at its input.
  *
  * @author Igor Konnov
  */
trait TlaModuleMixin {
  var tlaModule: Option[TlaModule]
}
