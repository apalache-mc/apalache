package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.tla.lir.{TlaModule, ModuleProperty, Transformations}

/**
 * A pass that receives a TLA+ module at its input.
 *
 * @author Igor Konnov
 */
trait TlaModuleMixin {
  protected var tlaModule: Option[TlaModule with Transformations] = None
  def updateModule(pass: Pass, currentModule: Option[TlaModule with Transformations], module: TlaModule): Unit = {
    val currentProperties: Set[ModuleProperty.Value] = if (currentModule.isDefined) currentModule.get.properties else Set()
    val newModule = module.asInstanceOf[TlaModule with Transformations]

    newModule.properties = currentProperties ++ pass.transformations
    tlaModule = Some(newModule)
  }
  def hasModule: Boolean = tlaModule.isDefined
  def unsafeGetModule: TlaModule with Transformations = tlaModule.get
}
