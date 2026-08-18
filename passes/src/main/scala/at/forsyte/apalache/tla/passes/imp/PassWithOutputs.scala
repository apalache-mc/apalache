package at.forsyte.apalache.tla.passes.imp

import at.forsyte.apalache.infra.passes.Pass
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.TlaModule

/**
 * A pass that outputs its results to the intermediate folder
 *
 * @author
 *   Jure Kukovec
 */
trait PassWithOutputs extends Pass {
  // TODO: This should get called automatically in PassChainExecutor after the refactoring associated with #858.
  //        Currently blocked by cyclic dependencies
  def writeOut(writerFactory: TlaWriterFactory, module: TlaModule): Unit = {
    val passNumString = f"${passNumber}%02d" // Leading 0s
    writerFactory.writeModuleAllFormats(module.copy(name = s"${passNumString}_Out${name}"), TlaWriter.STANDARD_MODULES)
  }

}
