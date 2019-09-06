package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.tla.lir.TlaModule

/**
  * A pass that receives a TLA+ module at its input.
  *
  * @author Igor Konnov
  */
trait TlaModuleMixin {
  private var tlaModule : Option[TlaModule] = None
  def setModule( module : TlaModule ) : Unit = {
    tlaModule = Some( module )
  }
}
