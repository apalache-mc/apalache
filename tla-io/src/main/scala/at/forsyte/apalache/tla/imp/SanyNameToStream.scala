package at.forsyte.apalache.tla.imp

import util.SimpleFilenameToStream

import java.io.File

/**
 * A decorator of SANY's SimpleFilenameToStream that rewires some names to Apalache names.
 *
 * @author
 *   Igor Konnov
 */
class SanyNameToStream extends SimpleFilenameToStream {
  override def resolve(name: String, isModule: Boolean): File = {
    val wiredOrOriginalName = StandardLibrary.wiredModules.getOrElse(name, name)
    super.resolve(wiredOrOriginalName, isModule)
  }
}
