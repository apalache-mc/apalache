package at.forsyte.apalache.tla.imp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.io.json.impl.{Type1TagReader, UJsonRep, UJsonToTla}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{CyclicDependencyError, TlaModule}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.standard.DeclarationSorter
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.imp.{SanyImporter, SanyImporterException}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

import java.io.File
import java.nio.file.Path

/**
 * Parsing TLA+ code with SANY.
 *
 * @author Igor Konnov
 */
class SanyParserPassImpl @Inject() (
    val options: PassOptions, val sourceStore: SourceStore, val annotationStore: AnnotationStore,
    val writerFactory: TlaWriterFactory, @Named("AfterParser") val nextPass: Pass with TlaModuleMixin
) extends SanyParserPass with LazyLogging {

  private var rootModule: Option[TlaModule] = None

  /**
   * The name of the pass
   *
   * @return the name associated with the pass
   */
  override def name: String = "SanyParser"

  /**
   * Run the pass
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    val filename = options.getOrError[String]("parser", "filename")
    if (filename.endsWith(".json")) {
      try {
        val moduleJson = UJsonRep(ujson.read(new File(filename)))
        val modules = new UJsonToTla(Some(sourceStore))(Type1TagReader).fromRoot(moduleJson)
        rootModule = modules match {
          case rMod +: Nil => Some(rMod)
          case _           => None
        }
      } catch {
        case e: Exception =>
          logger.error("  > " + e.getMessage)
          rootModule = None
      }
    } else {
      val (rootName, modules) =
        new SanyImporter(sourceStore, annotationStore)
          .loadFromFile(new File(filename))
      rootModule = modules.get(rootName)
    }
    rootModule match {
      case None =>
        logger.error("  > Error parsing file " + filename)
        false

      case Some(mod) =>
        // In rare cases, declarations may be out of order, as a result of substitution. Reorder them.
        rootModule =
          try {
            Some(DeclarationSorter.instance(mod))
          } catch {
            case e: CyclicDependencyError =>
              // re-throw the error for the nice error message
              throw new SanyImporterException(e.getMessage)
          }

        // save the output
        writerFactory.writeModuleAllFormats(rootModule.get.copy(name = "00_OutParser"), TlaWriter.STANDARD_MODULES)

        // write parser output to specified destination, if requested
        options.get[String]("parser", "output").foreach { output =>
          val writer = OutputManager.printWriter(output)

          if (filename.toLowerCase.endsWith(".tla")) {
            val moduleName = filename.substring(0, filename.length - ".tla".length)
            writerFactory.writeModuleToTla(rootModule.get.copy(name = moduleName), TlaWriter.STANDARD_MODULES,
                Some(writer))
          } else if (filename.toLowerCase.endsWith(".json")) {
            val moduleName = filename.substring(0, filename.length - ".json".length)
            writerFactory.writeModuleToJson(rootModule.get.copy(name = moduleName), TlaWriter.STANDARD_MODULES,
                Some(writer))
          } else {
            logger.error(s"  > Unrecognized file format: $filename. Supported formats: .tla and .json")
          }

          if (options.getOrElse[Boolean]("general", "debug", false)) {
            val sourceLocator =
              SourceLocator(sourceStore.makeSourceMap, new ChangeListener())
            rootModule.get.operDeclarations foreach sourceLocator.checkConsistency
          }
          if (options.getOrElse[Boolean]("general", "debug", false)) {
            val sourceLocator =
              SourceLocator(sourceStore.makeSourceMap, new ChangeListener())
            rootModule.get.operDeclarations foreach sourceLocator.checkConsistency
          }
        }

        true
    }
  }

  /**
   * Get the next pass in the chain. What is the next pass is up
   * to the module configuration and the pass outcome.
   *
   * @return the next pass, if exists, or None otherwise
   */
  override def next(): Option[Pass] =
    rootModule map { m =>
      nextPass.setModule(m)
      nextPass
    }
}
