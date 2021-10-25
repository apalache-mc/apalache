package at.forsyte.apalache.io.lir

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.lir.TlaModule
import OutputManager.Names._

import java.io.{File, FileWriter, PrintWriter}

/**
 * An interface for constructing instances of TlaWriter.
 *
 * @author Igor Konnov
 */
trait TlaWriterFactory {

  def createTlaWriter(printWriter: PrintWriter): TlaWriter

  def createJsonWriter(printWriter: PrintWriter): TlaWriter

  /**
   * Write a module to a file (without appending), in all supported formats (TLA+ and JSON).
   *
   * @param module       TLA module to write
   */
  def writeModuleAllFormats(module: TlaModule, extendedModuleNames: List[String]): Unit = {
    writeModuleToTla(module, extendedModuleNames)
    writeModuleToJson(module, extendedModuleNames)
  }

  // Internal call, parameterized by output format writer
  protected def writeModuleWithFormatWriter(extension: String, createWriter: PrintWriter => TlaWriter)(
      module: TlaModule, extendedModuleNames: List[String]): Unit =
    OutputManager.doIfFlag(IntermediateFlag) {
      OutputManager.runDirPathOpt.foreach { runDir =>
        val outDir = new File(runDir.toFile, IntermediateFoldername)
        if (!outDir.exists()) {
          outDir.mkdir()
        }
        val file = new File(outDir, module.name + extension)
        val writer = new PrintWriter(new FileWriter(file, false))
        try {
          createWriter(writer).write(module, extendedModuleNames)
        } finally {
          writer.close()
        }
      }
    }

  /**
   * Write a module to a file (without appending), in the TLA+ format.
   *
   * @param module TLA module to write
   */
  def writeModuleToTla(module: TlaModule, extendedModuleNames: List[String]): Unit =
    writeModuleWithFormatWriter(".tla", createTlaWriter)(module, extendedModuleNames)

  /**
   * Write a module to a file (without appending), in the Apalache JSON format.
   *
   * @param module TLA module to write
   */
  def writeModuleToJson(module: TlaModule, extendedModuleNames: List[String]): Unit =
    writeModuleWithFormatWriter(".json", createJsonWriter)(module, extendedModuleNames)
}
