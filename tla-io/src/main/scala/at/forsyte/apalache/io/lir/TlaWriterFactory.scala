package at.forsyte.apalache.io.lir

import at.forsyte.apalache.io.OutputWorkspace
import at.forsyte.apalache.tla.lir.TlaModule

import java.io.{File, PrintWriter}

/**
 * An interface for constructing instances of TlaWriter.
 *
 * @author
 *   Igor Konnov
 */
trait TlaWriterFactory {
  def createTlaWriter(printWriter: PrintWriter): TlaWriter

  def createJsonWriter(printWriter: PrintWriter): TlaWriter

  /**
   * Write a module to a file (without appending), in all supported formats (TLA+ and JSON).
   *
   * @param outputWorkspace
   *   output workspace in which to write the files
   * @param module
   *   TLA module to write
   * @param extendedModuleNames
   *   names of the modules to include in the module's `EXTENDS` declaration
   */
  def writeModuleAllFormats(
      outputWorkspace: OutputWorkspace,
      module: TlaModule,
      extendedModuleNames: List[String]): Unit = {
    writeModuleToTla(outputWorkspace, module, extendedModuleNames, None)
    writeModuleToJson(outputWorkspace, module, extendedModuleNames, None)
  }

  // Internal call, parameterized by output format writer
  //
  // if `writer` supplied, write the module to the given writer, otherwise
  // a default writer is constructed based on the file name, in the intermediate
  // output directory
  protected def writeModuleWithFormatWriter(
      outputWorkspace: OutputWorkspace,
      extension: String,
      createWriter: PrintWriter => TlaWriter,
      file: Option[File],
    )(module: TlaModule,
      extendedModuleNames: List[String]): Unit = {
    val writeHelper: (PrintWriter => Unit) => Unit = file match {
      case Some(f) => outputWorkspace.withWriter(f.toPath)
      case None    => outputWorkspace.withWriterInIntermediateDir(module.name + extension)
    }
    writeHelper(createWriter(_).write(module, extendedModuleNames))
  }

  /**
   * Write a module to a file (without appending), in the TLA+ format.
   *
   * @param outputWorkspace
   *   output workspace in which to write the file
   * @param module
   *   TLA module to write
   * @param extendedModuleNames
   *   names of the modules to include in the module's `EXTENDS` declaration
   * @param file
   *   target file, or `None` to write to a file derived from the module name in the intermediate output directory
   */
  def writeModuleToTla(
      outputWorkspace: OutputWorkspace,
      module: TlaModule,
      extendedModuleNames: List[String],
      file: Option[File]): Unit =
    writeModuleWithFormatWriter(outputWorkspace, ".tla", createTlaWriter, file)(module, extendedModuleNames)

  /**
   * Write a module to a file (without appending), in the Apalache JSON format.
   *
   * @param outputWorkspace
   *   output workspace in which to write the file
   * @param module
   *   TLA module to write
   * @param extendedModuleNames
   *   names of the modules to include in the module's `EXTENDS` declaration
   * @param file
   *   target file, or `None` to write to a file derived from the module name in the intermediate output directory
   */
  def writeModuleToJson(
      outputWorkspace: OutputWorkspace,
      module: TlaModule,
      extendedModuleNames: List[String],
      file: Option[File]): Unit =
    writeModuleWithFormatWriter(outputWorkspace, ".json", createJsonWriter, file)(module, extendedModuleNames)
}
