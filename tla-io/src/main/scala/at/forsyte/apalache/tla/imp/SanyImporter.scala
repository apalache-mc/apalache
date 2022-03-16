package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.TlaModule
import org.apache.commons.io.output.WriterOutputStream
import tla2sany.drivers.SANY
import tla2sany.modanalyzer.SpecObj

import java.io._
import java.nio.file.Files
import scala.io.Source
import scala.util.{Failure, Success, Try}

/**
 * This is the entry point for parsing TLA+ code with SANY and constructing an intermediate representation.
 *
 * @author
 *   konnov
 */
class SanyImporter(sourceStore: SourceStore, annotationStore: AnnotationStore) {

  /**
   * Load a TLA+ specification from a file by calling SANY.
   *
   * @param file
   *   an input file
   * @param useLibraryPaths
   *   Whether to include [[file]]'s containing directory as library path. Disable when you [[loadFromSource()]].
   * @return
   *   the pair (the root module name, a map of modules)
   */
  def loadFromFile(file: File, useLibraryPaths: Boolean = true): (String, Map[String, TlaModule]) = {
    // create a string buffer to write SANY's error messages
    // use.toString() to retrieve the error messages
    val errBuf = new StringWriter()

    // Resolver for filenames, patched for wired modules.
    // If `file` has a parent directory and `useLibraryPaths` is set, look up files in this parent directory.
    // Otherwise, look up files in the paths given by the `TLA-Library` Java system variable.
    // Compatible with TLC at commit https://github.com/tlaplus/tlaplus/commit/b905a86e31714bf5002290141b51b41ffe280c8e
    val filenameResolver = if (useLibraryPaths) {
      file.getParent() match {
        case null          => SanyNameToStream()
        case parentDirPath => SanyNameToStream(parentDirPath)
      }
    } else SanyNameToStream()

    // call SANY
    val specObj = new SpecObj(file.getAbsolutePath, filenameResolver)
    SANY.frontEndMain(
        specObj,
        file.getAbsolutePath,
        new PrintStream(new WriterOutputStream(errBuf, "UTF8")),
    )
    // abort on errors
    throwOnError(specObj)
    // do the translation
    val modmap = specObj.getExternalModuleTable.getModuleNodes
      .foldLeft(Map[String, TlaModule]()) { (map, node) =>
        map + (node.getName.toString ->
          ModuleTranslator(sourceStore, annotationStore).translate(node))
      }

    (specObj.getName, modmap)
  }

  /**
   * Load a TLA+ specification from a text source. This method creates a temporary file and saves the source's contents
   * into it, in order to call SANY.
   *
   * @param moduleName
   *   the name of the root module (SANY compares it against the filename, so we have to know it)
   * @param source
   *   the text source
   * @return
   *   the pair (the root module name, a map of modules)
   */
  def loadFromSource(
      moduleName: String,
      source: Source): (String, Map[String, TlaModule]) = {
    val tempDir = Files.createTempDirectory("sanyimp").toFile
    val temp = new File(tempDir, moduleName + ".tla")
    try {
      // write the contents to a temporary file
      val pw = new PrintWriter(temp)
      try {
        Try(source.getLines()) match {
          case Success(lines) => lines.foreach(line => pw.println(line))
          case Failure(e)     => throw new FileNotFoundException("Source not found: " + e.getMessage)
        }
      } finally {
        pw.close()
      }
      // Disable use of library paths, as we are loading from a [[Source]] object.
      // This prevents SANY from looking for wired modules ([[StandardLibrary.wiredModules]]) in `tempDir`.
      loadFromFile(temp, false)
    } finally {
      temp.delete()
      tempDir.delete()
    }
  }

  private def throwOnError(specObj: SpecObj): Unit = {
    val initErrors = specObj.getInitErrors
    if (initErrors.isFailure) {
      throw new SanyAbortException(initErrors.toString)
    }
    val contextErrors = specObj.getGlobalContextErrors
    if (contextErrors.isFailure) {
      throw new SanyAbortException(contextErrors.toString)
    }
    val parseErrors = specObj.getParseErrors
    if (parseErrors.isFailure) {
      throw new SanySyntaxException(parseErrors.toString)
    }
    val semanticErrors = specObj.getSemanticErrors
    if (semanticErrors.isFailure) {
      throw new SanySemanticException(semanticErrors.toString)
    }
    // the error level is above zero, so SANY failed for an unknown reason
    if (specObj.getErrorLevel > 0) {
      throw new SanyException(
          "Unknown SANY error (error level=%d)".format(specObj.getErrorLevel)
      )
    }
  }
}
