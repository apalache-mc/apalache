package at.forsyte.apalache.tla.imp.passes

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
  def writeOut(writerFactory: TlaWriterFactory, module: TlaModule): Unit = {
    val passNumString = f"${passNumber}%02d" // Leading 0s
    writerFactory.writeModuleAllFormats(module.copy(name = s"${passNumString}_Out${name}"), TlaWriter.STANDARD_MODULES)
  }

}
