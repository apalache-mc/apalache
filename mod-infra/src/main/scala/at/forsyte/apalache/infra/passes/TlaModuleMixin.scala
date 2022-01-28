package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.tla.lir.{TlaModule, TransformedTlaModule, ModuleProperty}

/**
 * A pass that receives a TLA+ module at its input.
 *
 * @author Igor Konnov
 */
trait TlaModuleMixin {
  protected var tlaModule: Option[TransformedTlaModule] = None
  def updateModule(pass: Pass, currentModule: Option[TransformedTlaModule], module: TlaModule): Unit = {
    val properties: Set[ModuleProperty.Value] = if (currentModule.isDefined) currentModule.get.properties else Set()
    tlaModule = Some(new TransformedTlaModule(module, properties ++ pass.transformations))
  }
  def hasModule: Boolean = tlaModule.isDefined
  def unsafeGetModule: TransformedTlaModule = tlaModule.get
}
