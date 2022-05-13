package at.forsyte.apalache.tla.imp.passes

import at.forsyte.apalache.infra.ExitCodes
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.io.json.impl.{DefaultTagReader, UJsonRep, UJsonToTla}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{CyclicDependencyError, TlaModule}
import at.forsyte.apalache.tla.lir.transformations.standard.DeclarationSorter
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.imp.{utils, SanyImporter, SanyImporterException}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

import java.io.File

/**
 * Parsing TLA+ code with SANY.
 *
 * @author
 *   Igor Konnov
 */
class SanyParserPassImpl @Inject() (
    val options: PassOptions,
    val sourceStore: SourceStore,
    val annotationStore: AnnotationStore,
    val writerFactory: TlaWriterFactory)
    extends SanyParserPass with LazyLogging {

  override def name: String = "SanyParser"

  override def execute(module: TlaModule): PassResult = {
    val filename = options.getOrError[String]("parser", "filename")
    var rootModule: TlaModule = if (filename.endsWith(".json")) {
      try {
        val moduleJson = UJsonRep(ujson.read(new File(filename)))
        val modules = new UJsonToTla(Some(sourceStore))(DefaultTagReader).fromRoot(moduleJson)
        modules match {
          case rMod +: Nil => rMod
          case _ => {
            logger.error("  > Error parsing file " + filename)
            return Left(ExitCodes.ERROR_SPEC_PARSE)
          }
        }
      } catch {
        case e: Exception =>
          logger.error("  > Error parsing file " + filename)
          logger.error("  > " + e.getMessage)
          return Left(ExitCodes.ERROR_SPEC_PARSE)
      }
    } else {
      val (rootName, modules) =
        new SanyImporter(sourceStore, annotationStore)
          .loadFromFile(new File(filename))
      modules.get(rootName).get
    }

    rootModule =
      try {
        DeclarationSorter.instance(rootModule)
      } catch {
        case e: CyclicDependencyError =>
          // re-throw the error for the nice error message
          throw new SanyImporterException(e.getMessage)
      }

    // save the output
    writeOut(writerFactory, rootModule)

    // write parser output to specified destination, if requested
    utils.writeToOutput(rootModule, options, writerFactory, logger, sourceStore)

    Right(rootModule)
  }

  override def dependencies = Set()

  override def transformations = Set()
}
