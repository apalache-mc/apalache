package at.forsyte.apalache.tla.imp

import util.SimpleFilenameToStream

import java.io.File

/**
 * A decorator of SANY's SimpleFilenameToStream that rewires some names to Apalache names.
 *
 * @author
 *   Igor Konnov, Thomas Pani
 */
trait SanyNameToStream extends SimpleFilenameToStream {
  override def resolve(name: String, isModule: Boolean): File = {
    val wiredOrOriginalName = StandardLibrary.wiredModules.getOrElse(name, name)
    super.resolve(wiredOrOriginalName, isModule)
  }
}

/**
 * A decorator of SANY's SimpleFilenameToStream that rewires some names to Apalache names.
 */
object SanyNameToStream {

  /**
   * Construct a filename resolver that looks for files (in this order) in
   *   1. the library paths in the `TLA-Library` Java system variable,
   *   1. SANY's base path (package `tla2sany.StandardModules` in `tla2tools.jar`)
   *
   * @see
   *   [docs/apalache/running.md#module-lookup]
   */
  def apply() = new SimpleFilenameToStream() with SanyNameToStream

  /**
   * Construct a filename resolver that looks for files (in this order) in
   *   1. the path given by parameter `libraryPath`, and
   *   1. SANY's base path (package `tla2sany.StandardModules` in `tla2tools.jar`)
   *
   * @see
   *   [docs/apalache/running.md#module-lookup]
   */
  def apply(libraryPath: String) = new SimpleFilenameToStream(libraryPath) with SanyNameToStream
}
