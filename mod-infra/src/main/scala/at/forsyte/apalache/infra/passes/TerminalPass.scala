package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.tla.lir.ModuleProperty

/**
 * This pass does nothing but it can be used to collect the output of the final pass.
 */
class TerminalPass extends Pass {

  override def name: String = "Terminal"

  override def execute(): Boolean = {
    true
  }

  override def nextPass = new TerminalPassWithTlaModule

  override def dependencies: Set[ModuleProperty.Value] = Set()

  override def transformations: Set[ModuleProperty.Value] = Set()
}
