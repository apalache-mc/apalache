package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.TlaModule
import com.typesafe.scalalogging.LazyLogging
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
 *   Igor Konnov, Thomas Pani
 */
class SanyImporter(sourceStore: SourceStore, annotationStore: AnnotationStore) extends LazyLogging {

  /**
   * Load a TLA+ specification from a file by calling SANY.
   *
   * @param file
   *   an input file
   * @return
   *   the pair (the root module name, a map of modules)
   */
  def loadFromFile(file: File): (String, Map[String, TlaModule]) = {
    // create a string buffer to write SANY's error messages
    // use.toString() to retrieve the error messages
    val errBuf = new StringWriter()

    // Construct library lookup path:
    //   1. Include the file's parent directory
    val parentDirPath = file.getAbsoluteFile().getParent() match {
      case null                  => Nil
      case parentDirPath: String => Seq(parentDirPath)
    }
    //   2. Patch in Apalache standard library.
    //      When running Apalache from the fat JAR, these TLA+ modules are baked into the JAR.
    //      Otherwise (e.g., running from `sbt`, an IDE, for unit tests), we include the standard library path for
    //      lookup from the filesystem.
    val standardLibraryPath = {
      // Test if running from fat JAR; see also `build.sbt` and [[StandardLibrary.wiredModules]]
      if (this.getClass().getClassLoader().getResource("tla2sany/StandardModules/Apalache.tla") != null) {
        // Running from fat JAR with standard library baked in (in `build.sbt`).
        // SANY looks up modules from the JAR as part of its base path, no need to adjust the lookup paths.
        Nil
      } else {
        // Running from outside the fat JAR, we don't have a standard library bundled.
        // Add $APALACHE_HOME/src/tla/ to lookup paths.
        System.getenv("APALACHE_HOME") match {
          // Warn if environment variable APALACHE_HOME is not set
          case null =>
            logger.warn("Not running from fat JAR and APALACHE_HOME is not set;")
            logger.warn("will not be able to find the Apalache standard library.")
            Nil
          case apalacheHome: String => Seq(s"${apalacheHome}/src/tla")
        }
      }
    }
    val libraryPaths = parentDirPath ++ standardLibraryPath

    // Resolver for filenames, patched for wired modules.
    val filenameResolver = SanyNameToStream(libraryPaths)

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
      loadFromFile(temp)
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
