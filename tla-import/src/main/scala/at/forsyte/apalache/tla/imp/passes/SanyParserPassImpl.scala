package at.forsyte.apalache.tla.imp.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.lir.io.{JsonReader, JsonWriter, PrettyWriter}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
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
class SanyParserPassImpl @Inject()(
                                    val options: PassOptions,
                                    val sourceStore: SourceStore,
                                    val annotationStore: AnnotationStore,
                                    @Named("AfterParser") val nextPass: Pass with TlaModuleMixin
) extends SanyParserPass
    with LazyLogging {

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
        rootModule = Some(JsonReader.readModule(new File(filename)))
      } catch {
        case e: Exception =>
          logger.error("  > " + e.getMessage)
          rootModule = None
      }
    } else {
      val (rootName, modules) =
        new SanyImporter(sourceStore, annotationStore).loadFromFile(new File(filename))
      rootModule = modules.get(rootName)
    }
    if (rootModule.isEmpty) {
      logger.error("  > Error parsing file " + filename)
    } else {
      val outdir = options.getOrError("io", "outdir").asInstanceOf[Path]
      PrettyWriter.write(
        rootModule.get,
        new File(outdir.toFile, "out-parser.tla")
      )
      JsonWriter.write(
        rootModule.get,
        new File(outdir.toFile, "out-parser.json")
      )

      // write parser output to specified destination, if requested
      val output = options.getOrElse("parser", "output", "")
      if (output.nonEmpty) {
        if (output.contains(".tla"))
          PrettyWriter.write(rootModule.get, new File(output))
        else if (output.contains(".json"))
          JsonWriter.write(rootModule.get, new File(output))
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
    }
    rootModule.isDefined
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
