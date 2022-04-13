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
   *   1. the paths given by parameter `libraryPaths`, and
   *   1. SANY's base path (package `tla2sany.StandardModules` in `tla2tools.jar`)
   *
   * @see
   *   [docs/apalache/running.md#module-lookup]
   */
  def apply(libraryPaths: Seq[String]) = new SimpleFilenameToStream(libraryPaths.toArray) with SanyNameToStream
}
