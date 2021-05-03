package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.TlaModule

import java.io.{File, FileWriter, PrintWriter}

/**
 * An interface for constructing instances of TlaWriter.
 *
 * @author Igor Konnov
 */
trait TlaWriterFactory {

  def create(printWriter: PrintWriter): TlaWriter

  /**
   * Write a module to a file (without appending).
   *
   * @param module     a TLA module
   * @param outputFile an output file that will be created or overwritten
   */
  def writeModuleToFile(module: TlaModule, extendedModuleNames: List[String], outputFile: File): Unit = {
    val writer = new PrintWriter(new FileWriter(outputFile, false))
    try {
      create(writer).write(module, extendedModuleNames)
    } finally {
      writer.close()
    }
  }

}
