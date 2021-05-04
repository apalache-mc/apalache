package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir.TlaModule

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
  def writeModuleAllFormats(module: TlaModule, extendedModuleNames: List[String], outDirectory: File): Unit = {
    writeModuleToTla(module, extendedModuleNames, outDirectory)
    writeModuleToJson(module, extendedModuleNames, outDirectory)
  }

  /**
   * Write a module to a file (without appending), in the TLA+ format.
   *
   * @param module       TLA module to write
   * @param outDirectory output directory
   */
  def writeModuleToTla(module: TlaModule, extendedModuleNames: List[String], outDirectory: File): Unit = {
    val file = new File(outDirectory, module.name + ".tla")
    val writer = new PrintWriter(new FileWriter(file, false))
    try {
      createTlaWriter(writer).write(module, extendedModuleNames)
    } finally {
      writer.close()
    }
  }

  /**
   * Write a module to a file (without appending), in the Apalache JSON format.
   *
   * @param module       TLA module to write
   * @param outDirectory output directory
   */
  def writeModuleToJson(module: TlaModule, extendedModuleNames: List[String], outDirectory: File): Unit = {
    val file = new File(outDirectory, module.name + ".json")
    val writer = new PrintWriter(new FileWriter(file, false))
    try {
      createJsonWriter(writer).write(module, extendedModuleNames)
    } finally {
      writer.close()
    }
  }

}
