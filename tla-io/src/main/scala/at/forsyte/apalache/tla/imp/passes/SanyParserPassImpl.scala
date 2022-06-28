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

  private def loadFromJson(filename: String): PassResult = {
    try {
      val moduleJson = UJsonRep(ujson.read(new File(filename)))
      val modules = new UJsonToTla(Some(sourceStore))(DefaultTagReader).fromRoot(moduleJson)
      modules match {
        case rMod +: Nil => Right(rMod)
        case _ => {
          logger.error("  > Error parsing file " + filename)
          Left(ExitCodes.ERROR_SPEC_PARSE)
        }
      }
    } catch {
      case e: Exception =>
        logger.error("  > Error parsing file " + filename)
        logger.error("  > " + e.getMessage)
        Left(ExitCodes.ERROR_SPEC_PARSE)
    }
  }

  private def loadFromFile(filename: String): PassResult = {
    val (rootName, modules) =
      new SanyImporter(sourceStore, annotationStore)
        .loadFromFile(new File(filename))
    Right(modules.get(rootName).get)
  }

  private def saveLoadedModule(module: TlaModule): Either[ExitCodes.TExitCode, Unit] = {
    // save the output
    writeOut(writerFactory, module)
    // write parser output to specified destination, if requested
    utils.writeToOutput(module, options, writerFactory, logger, sourceStore)
    Right(())
  }

  protected def sortDeclarations(module: TlaModule): PassResult = {
    try {
      Right(DeclarationSorter.instance(module))
    } catch {
      case e: CyclicDependencyError =>
        // re-throw the error for the nice error message
        throw new SanyImporterException(e.getMessage)
    }
  }

  override def execute(module: TlaModule): PassResult = {
    val filename = options.getOrError[String]("parser", "filename")
    for {
      rootModule <-
        if (filename.endsWith(".json")) {
          loadFromJson(filename)
        } else {
          loadFromFile(filename)
        }.flatMap(sortDeclarations)

      _ <- saveLoadedModule(rootModule)
    } yield rootModule
  }

  override def dependencies = Set()

  override def transformations = Set()
}
