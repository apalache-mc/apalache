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
   * @param outDirectory output directory
   */
  def writeModuleAllFormats(module: TlaModule, extendedModuleNames: List[String]): Unit = {
    writeModuleToTla(module, extendedModuleNames)
    writeModuleToJson(module, extendedModuleNames)
  }

  /**
   * Write a module to a file (without appending), in the TLA+ format.
   *
   * @param module       TLA module to write
   * @param outDirectory output directory
   */
  def writeModuleToTla(module: TlaModule, extendedModuleNames: List[String]): Unit =
    OutputManager.doIfFlag(INTERMEDIATE_FLAG) {
      OutputManager.inRunDir { runDir =>
        val outDir = new File(runDir.toFile, INTERMEDIATE_FOLDERNAME)
        if (!outDir.exists()) {
          outDir.mkdir()
        }
        val file = new File(outDir, module.name + ".tla")
        val writer = new PrintWriter(new FileWriter(file, false))
        try {
          createTlaWriter(writer).write(module, extendedModuleNames)
        } finally {
          writer.close()
        }
      }
    }

  /**
   * Write a module to a file (without appending), in the Apalache JSON format.
   *
   * @param module       TLA module to write
   * @param outDirectory output directory
   */
  def writeModuleToJson(module: TlaModule, extendedModuleNames: List[String]): Unit =
    OutputManager.doIfFlag(INTERMEDIATE_FLAG) {
      OutputManager.inRunDir { runDir =>
        val outDir = new File(runDir.toFile, INTERMEDIATE_FOLDERNAME)
        if (!outDir.exists()) {
          outDir.mkdir()
        }
        val file = new File(outDir, module.name + ".json")
        val writer = new PrintWriter(new FileWriter(file, false))
        try {
          createJsonWriter(writer).write(module, extendedModuleNames)
        } finally {
          writer.close()
        }
      }
    }
}
