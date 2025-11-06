package at.forsyte.apalache.tla.passes.imp

import at.forsyte.apalache.infra.ExitCodes
import at.forsyte.apalache.infra.passes.Pass.{PassFailure, PassResult}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.io.json.impl.DefaultTagJsonReader
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{CyclicDependencyError, TlaModule}
import at.forsyte.apalache.tla.lir.transformations.standard.DeclarationSorter
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.imp.{utils, SanyImporter, SanyImporterException}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

import java.io.File
import at.forsyte.apalache.infra.passes.options.SourceOption
import scala.io.Source
import at.forsyte.apalache.infra.passes.options.OptionGroup
import scala.util.Try
import scala.util.Failure
import scala.util.Success
import at.forsyte.apalache.tla.imp.SanyException
import at.forsyte.apalache.io.annotations.AnnotationParserError
import at.forsyte.apalache.io.json.impl.ujson.{UJsonRep, UJsonToTla}
import at.forsyte.apalache.io.quint.{Quint, QuintOutput}

/**
 * Parsing TLA+ code with SANY.
 *
 * @author
 *   Igor Konnov
 */
class SanyParserPassImpl @Inject() (
    val options: OptionGroup.HasIO,
    val sourceStore: SourceStore,
    val annotationStore: AnnotationStore,
    val writerFactory: TlaWriterFactory)
    extends SanyParserPass with LazyLogging {

  override def name: String = "SanyParser"

  private def loadFromJsonSource(source: SourceOption): PassResult = {
    import SourceOption._

    val result = for {
      module <- source.format match {
        case Format.Qnt =>
          for {
            source <- source.getContent
            quintOutput <- QuintOutput.read(source)
            tla <- new Quint(quintOutput).tlaModule(quintOutput.modules(0))
          } yield tla
        case Format.Json =>
          for {
            str <- source.getContent
            json <- Try(UJsonRep(ujson.read(str)))
            tla <- new UJsonToTla(Some(sourceStore))(DefaultTagJsonReader).fromSingleModule(json)
          } yield tla
        case _ => throw new IllegalArgumentException(s"loadFromJsonSource called with non Json SourceOption ${source}")
      }
    } yield module

    result match {
      case Success(mod) => Right(mod)
      case Failure(err) =>
        logger.error(s"  > Error parsing file ${source}")
        logger.error("  > " + err.getMessage)
        passFailure(err.getMessage(), ExitCodes.ERROR_SPEC_PARSE)
    }
  }

  private def loadFromTlaFile(file: File): PassResult = {
    val (rootName, modules) =
      new SanyImporter(sourceStore, annotationStore)
        .loadFromFile(file)
    Right(modules.get(rootName).get)
  }

  private def loadFromTlaString(content: String, aux: Seq[String]): PassResult = {
    val (rootName, modules) =
      new SanyImporter(sourceStore, annotationStore)
        .loadFromSource(Source.fromString(content), aux.map(Source.fromString(_)))
    Right(modules.get(rootName).get)
  }

  private val loadFromTlaSource: SourceOption => PassResult = {
    case SourceOption.StringSource(content, aux, _) => loadFromTlaString(content, aux)
    case SourceOption.FileSource(file, _)           => loadFromTlaFile(file)
  }

  private def saveLoadedModule(module: TlaModule): Either[PassFailure, Unit] = {
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

  override def dependencies = Set()

  override def transformations = Set()

  override def execute(module: TlaModule): PassResult = {
    try {
      parseSource(options.input.source)
    } catch {
      case err: SanyException         => reportErr(err.getMessage)
      case err: AnnotationParserError => reportErr(s"Syntax error in annotation: ${err.getMessage()}")
    }
  }

  private def reportErr(msg: String): PassResult = {
    logger.error(s"Parsing error: ${msg}")
    passFailure(List(msg), ExitCodes.ERROR)
  }

  private def parseSource(src: SourceOption): PassResult = {
    import SourceOption.Format._
    for {
      rootModule <- src.format match {
        case Itf          => throw new SanyImporterException("Parsing the ITF format is not supported")
        case (Json | Qnt) => loadFromJsonSource(src)
        case Tla          => loadFromTlaSource(src)
      }
      sortedModule <- sortDeclarations(rootModule)
      _ <- saveLoadedModule(sortedModule)
    } yield sortedModule

  }
}
