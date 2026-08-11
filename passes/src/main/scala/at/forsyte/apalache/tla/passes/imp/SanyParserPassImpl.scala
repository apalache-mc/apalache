package at.forsyte.apalache.tla.passes.imp

import at.forsyte.apalache.infra.{ExitCodes, PassOptionException}
import at.forsyte.apalache.infra.passes.Pass.{PassFailure, PassResult}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.lir.src.SourceStore
import at.forsyte.apalache.tla.lir.{CyclicDependencyError, TlaModule}
import at.forsyte.apalache.tla.lir.transformations.standard.DeclarationSorter
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.imp.{utils, SanyImporter, SanyImporterException}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

import java.io.File
import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.OutputWorkspace
import at.forsyte.apalache.io.config.{CommonOptions, ModuleIoOptions}

import scala.io.Source
import scala.util.Try
import scala.util.Failure
import scala.util.Success
import at.forsyte.apalache.tla.imp.SanyException
import at.forsyte.apalache.io.annotations.AnnotationParserError
import at.forsyte.apalache.io.json.DefaultTagJsonReader
import at.forsyte.apalache.io.json.ujsonimpl.{UJsonRepresentation, UJsonToTla}
import at.forsyte.apalache.io.quint.{Quint, QuintOutput}

/**
 * Parsing TLA+ code with SANY.
 *
 * @author
 *   Igor Konnov
 */
class SanyParserPassImpl @Inject() (
    val commonOptions: CommonOptions,
    val moduleIoOptions: ModuleIoOptions,
    val sourceStore: SourceStore,
    val annotationStore: AnnotationStore,
    outputWorkspace: OutputWorkspace,
    val writerFactory: TlaWriterFactory)
    extends SanyParserPass with LazyLogging {

  override def name: String = "SanyParser"

  private def loadFromJsonSource(source: InputSource): PassResult = {
    import InputSource._

    def readContent(): Try[String] = {
      val result = source.readUtf8
      if (result.isSuccess) Success(result.requireValue())
      else Failure(new PassOptionException(result.errors.mkString("; ")))
    }

    val result = for {
      module <- source.format match {
        case Format.Qnt =>
          for {
            content <- readContent()
            quintOutput <- QuintOutput.read(content)
            tla <- new Quint(quintOutput).tlaModule(quintOutput.modules(0))
          } yield tla
        case Format.Json =>
          for {
            str <- readContent()
            json <- Try(UJsonRepresentation(ujson.read(str)))
            tla <- new UJsonToTla(Some(sourceStore))(DefaultTagJsonReader).fromSingleModule(json)
          } yield tla
        case _ => throw new IllegalArgumentException(s"loadFromJsonSource called with non-JSON InputSource: $source")
      }
    } yield module

    result match {
      case Success(mod) => Right(mod)
      case Failure(err) =>
        logger.error(s"  > Error parsing file ${source}")
        logger.error("  > " + err.getMessage)
        passFailure(err.getMessage, ExitCodes.ERROR_SPEC_PARSE)
    }
  }

  private def loadFromTlaFile(file: File): PassResult = {
    val (rootName, modules) =
      new SanyImporter(sourceStore, annotationStore)
        .loadFromFile(file)
    Right(modules(rootName))
  }

  private def loadFromTlaString(content: String, aux: Seq[String]): PassResult = {
    val (rootName, modules) =
      new SanyImporter(sourceStore, annotationStore)
        .loadFromSource(Source.fromString(content), aux.map(Source.fromString))
    Right(modules(rootName))
  }

  private val loadFromTlaSource: InputSource => PassResult = {
    case value: InputSource.StringSource => loadFromTlaString(value.content, value.aux)
    case InputSource.FileSource(path, _) => loadFromTlaFile(path.toFile)
  }

  private def saveLoadedModule(module: TlaModule): Either[PassFailure, Unit] = {
    // save the output
    writeOut(writerFactory, outputWorkspace, module)
    // write parser output to specified destination, if requested
    utils.writeToOutput(
        module,
        commonOptions,
        moduleIoOptions.output,
        writerFactory,
        outputWorkspace,
        logger,
        sourceStore,
    )
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
      parseSource(moduleIoOptions.source)
    } catch {
      case err: SanyException         => reportErr(err.getMessage)
      case err: AnnotationParserError => reportErr(s"Syntax error in annotation: ${err.getMessage()}")
    }
  }

  private def reportErr(msg: String): PassResult = {
    logger.error(s"Parsing error: ${msg}")
    passFailure(List(msg), ExitCodes.ERROR)
  }

  private def parseSource(src: InputSource): PassResult = {
    import InputSource.Format._
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
