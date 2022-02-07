package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.tla.lir.{TlaModule, ModuleProperty}

/**
 * This pass does nothing but it can be used to collect the output of the final pass.
 */
class TerminalPass extends Pass {

  override def name: String = "Terminal"

  override def execute(module: TlaModule): Option[TlaModule] = {
    None
  }

  override def dependencies: Set[ModuleProperty.Value] = Set()

  override def transformations: Set[ModuleProperty.Value] = Set()
}
