package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.TransformedTlaModule

/**
 * A pass that receives a TLA+ module at its input.
 *
 * @author Igor Konnov
 */
trait TlaModuleMixin {
  protected var tlaModule: Option[TransformedTlaModule] = None
  def setModule(module: TransformedTlaModule): Unit = {
    tlaModule = Some(module)
  }
  def unsafeGetModule: TransformedTlaModule = tlaModule.get
}
