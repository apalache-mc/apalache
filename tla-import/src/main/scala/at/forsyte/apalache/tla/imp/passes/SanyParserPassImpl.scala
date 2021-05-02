package at.forsyte.apalache.tla.imp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.io.json.impl.{TlaToUJson, UJsonRep, UJsonToTla}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{CyclicDependencyError, TlaModule}
import at.forsyte.apalache.tla.lir.io.{TlaWriterFactory, UntypedReader}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.standard.DeclarationSorter
import at.forsyte.apalache.tla.lir.io.TlaType1PrinterPredefs.printer
import at.forsyte.apalache.tla.imp.{SanyImporter, SanyImporterException}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.io.{JsonReader, JsonWriter, TlaWriter, TlaWriterFactory}
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.Path

/**
 * Parsing TLA+ code with SANY.
 *
 * @author Igor Konnov
 */
class SanyParserPassImpl @Inject() (
    val options: PassOptions, val sourceStore: SourceStore, val changeListener: ChangeListener,
    val annotationStore: AnnotationStore, val writerFactory: TlaWriterFactory,
    @Named("AfterParser") val nextPass: Pass with TlaModuleMixin
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
    val filename = options.getOrError("parser", "filename").asInstanceOf[String]
    if (filename.endsWith(".json")) {
      try {
        val moduleJson = UJsonRep(ujson.read(new File(filename)))
        // TODO: Implement a TagReader in issue #780
        val modules = new UJsonToTla(Some(sourceStore))(UntypedReader).fromRoot(moduleJson)
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
        val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
        writerFactory.writeModuleToFile(rootModule.get, TlaWriter.STANDARD_MODULES,
            new File(outdir.toFile, "out-parser.tla"))
        writeJson(rootModule.get, new File(outdir.toFile, "out-parser.json"))

        // write parser output to specified destination, if requested
        val output = options.getOrElse("parser", "output", "")
        if (output.nonEmpty) {
          if (output.contains(".tla"))
            writerFactory.writeModuleToFile(rootModule.get, TlaWriter.STANDARD_MODULES, new File(output))
          else if (output.contains(".json"))
            writeJson(rootModule.get, new File(output))
          else
            logger.error(
                "  > Error writing output: please give either .tla or .json filename"
            )

          if (options.getOrElse("general", "debug", false)) {
            val sourceLocator =
              SourceLocator(sourceStore.makeSourceMap, new ChangeListener())
            rootModule.get.operDeclarations foreach sourceLocator.checkConsistency
          }
          if (options.getOrElse("general", "debug", false)) {
            val sourceLocator =
              SourceLocator(sourceStore.makeSourceMap, new ChangeListener())
            rootModule.get.operDeclarations foreach sourceLocator.checkConsistency
          }
        }

        true
    }
  }

  private def writeJson(module: TlaModule, file: File): Unit = {
    val writer = new PrintWriter(new FileWriter(file, false))
    try {
      val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)
      val jsonText = new TlaToUJson(Some(sourceLocator)).makeRoot(Seq(module)).toString
      writer.write(jsonText)
    } finally {
      writer.close()
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
