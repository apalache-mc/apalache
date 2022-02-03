package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.tla.lir.{TlaModule, ModuleProperty, TlaModuleProperties}

/**
 * A pass that receives a TLA+ module at its input.
 *
 * @author Igor Konnov, Gabriela Mafra
 */
trait TlaModuleMixin {

  /**
   * Stores a mutable TLA Module
   *
   * @return the stored TLA Module if exists, or None otherwise
   */
  var tlaModule: Option[TlaModule with TlaModuleProperties] = None

  /**
   * Updates the stored TLA Module, aggregating information from an origin pass
   *
   * @param pass  The pass that's performing the change
   * @param module  The new TLA Module to be set
   *
   * @returns nothing
   */
  def updateModule(pass: Pass with TlaModuleMixin, module: TlaModule): Unit = {
    val currentModule = pass.tlaModule
    val currentProperties: Set[ModuleProperty.Value] =
      if (currentModule.isDefined) currentModule.get.properties else Set()
    val newModule = new TlaModule(module.name, module.declarations) with TlaModuleProperties

    newModule.properties = currentProperties ++ pass.transformations
    tlaModule = Some(newModule)
  }

  /**
   * Checks if there is some TLA Module stored
   *
   * @return whether there is a TLA Module stored
   */
  def hasModule: Boolean = tlaModule.isDefined

  /**
   * Casts the stored TLA Module to a simple TlaModule, without the TlaModuleProperties trait
   *
   * @return the stored TLA Module without TlaModuleProperties
   */
  def rawModule: Option[TlaModule] = tlaModule
}
