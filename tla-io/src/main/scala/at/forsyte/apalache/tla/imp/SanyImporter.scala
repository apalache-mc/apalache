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
import java.nio.charset.StandardCharsets

// The SANY parser is not thread safe. This singleton object is used to create a
// mutex around its execution.
//
// We use the `synchronized` method of `AnyRef` to manage our mutex. See
//
//  - https://twitter.github.io/scala_school/concurrency.html#danger
//  - https://www.scala-lang.org/api/current/scala/AnyRef.html#synchronized[T0](x$1:=%3ET0):T0
//
// For more context on the SANY concurrency issues see https://github.com/apalache-mc/apalache/issues/1963
//
// All invocation of SANY should go through a synchronized method in this object.
object SANYSyncWrapper {
  def loadSpecObject(specObj: SpecObj, file: File, errBuf: Writer): Int = {
    this.synchronized {
      val outStream = WriterOutputStream
        .builder()
        .setWriter(errBuf)
        .setCharset(StandardCharsets.UTF_8)
        .get()
      SANY.frontEndMain(
          specObj,
          file.getAbsolutePath,
          new PrintStream(outStream),
      )
    }
  }
}

/**
 * This is the entry point for parsing TLA+ code with SANY and constructing an intermediate representation.
 *
 * @author
 *   Igor Konnov, Thomas Pani, Shon Feder
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

    // Set a unique tmpdir to avoid race-condition in SANY
    // TODO: RM once https://github.com/tlaplus/tlaplus/issues/688 is fixed
    System.setProperty("java.io.tmpdir", sanyTempDir().toString())

    // call SANY
    val specObj = new SpecObj(file.getAbsolutePath, filenameResolver)
    SANYSyncWrapper.loadSpecObject(specObj, file, errBuf)

    // abort on errors
    throwOnError(specObj)
    // do the translation
    val modmap = specObj.getExternalModuleTable.getModuleNodes
      .foldLeft(Map[String, TlaModule]()) { (map, node) =>
        map + (node.getName.toString ->
          ModuleTranslator(sourceStore, annotationStore).translate(node))
      }

    specObj.getName match {
      case null => throw new SanyImporterException("No root module defined in file")
      case name => (name, modmap)
    }
  }

  /**
   * Load a TLA+ specification from a text source, possibly including auxiliary modules needed for imports. This method
   * creates temporary files and saves the sources contents into it, in order to call SANY.
   *
   * @param source
   *   the text source for the root module
   * @param aux
   *   the text sources for any auxiliary modules
   * @return
   *   the pair (the root module name, a map of modules)
   */
  def loadFromSource(source: Source, aux: Seq[Source] = Seq()): (String, Map[String, TlaModule]) = {
    val tempDir = sanyTempDir()
    val nameAndModule = for {
      (rootName, rootFile) <- saveTlaFile(tempDir, source)
      // Save the aux modules to files, and get just the module names, if errors are hit, the first one will turn into a `Try`
      savedModuleNames <- Try(aux.map(saveTlaFile(tempDir, _).map(_._1).get))
      _ <- ensureModuleNamesAreUnique(rootName +: savedModuleNames)
      result <- Try(loadFromFile(rootFile))
    } yield result
    tempDir.delete()
    // Raise any errors previously captures in the `Try`
    nameAndModule.get
  }

  // Create a unique temp directory for use by the SANY importer
  private def sanyTempDir() = Files.createTempDirectory("sanyimp").toFile

  private def ensureModuleNamesAreUnique(moduleNames: Seq[String]): Try[Unit] = {
    val duplicateNames = moduleNames.groupBy(identity).filter(_._2.size > 1)
    if (duplicateNames.isEmpty) {
      Success(())
    } else {
      Failure(new SanyImporterException(
              s"Modules with duplicate names were supplied when loading from sources: ${duplicateNames.keySet}"))
    }
  }

  // Regex to match the module line and capture the module name
  private val MODULE_LINE_RE = """-+ +MODULE +(\w*) -+""".r

  // Try to extract the name of a module from the source specifying the module.
  //
  // This function copies the Source [s] and doesn't consume it.
  private def moduleNameOfSource(s: Source): Try[String] = {
    // Copy the source so we don't consume iterator
    val copy = s.reset()
    for {
      lines <- Try(copy.getLines()).recoverWith(e =>
        Failure(new FileNotFoundException("Source not found: " + e.getMessage)))
      firstLine = lines.nextOption().getOrElse("")
      moduleName <- (Iterator(firstLine) ++ lines).find(MODULE_LINE_RE.matches(_)) match {
        case Some(MODULE_LINE_RE(name)) => Success(name)
        case _                          =>
          Failure(
              new SanyImporterException(s"No module name found in source for module beginning with line ${firstLine}"))
      }
    } yield moduleName
  }

  private def saveTlaFile(dir: File, source: Source): Try[(String, File)] =
    for {
      moduleName <- moduleNameOfSource(source)
      tempFile = new File(dir, moduleName + ".tla")
      // write the contents to a tempFileorary file
      pw = new PrintWriter(tempFile)
      _ <- {
        // Stash the try result so we can close the pw before bailing if anything goes wrong
        val result = Try(source.getLines().foreach(pw.println(_)))
        pw.close()
        result
      }
    } yield (moduleName, tempFile)

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
