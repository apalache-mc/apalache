package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.io.OutputManager.Names.IntermediateFoldername
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.{ModuleProperty, TlaModule, TypeTag, UID, Untyped}
import at.forsyte.apalache.tla.typecheck.TypeCheckerTool
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs.printer
import at.forsyte.apalache.tla.imp.utils
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.Path

class EtcTypeCheckerPassImpl @Inject() (val options: PassOptions, val sourceStore: SourceStore,
    changeListener: ChangeListener, tracker: TransformationTracker, val annotationStore: AnnotationStore,
    val writerFactory: TlaWriterFactory)
    extends EtcTypeCheckerPass with LazyLogging {

  protected def inferPoly: Boolean = options.getOrElse[Boolean]("typecheck", "inferPoly", true)

  protected def passNumber: String = "01"

  override def name: String = "TypeCheckerSnowcat"

  override def execute(tlaModule: TlaModule): Option[TlaModule] = {
    logger.info(" > Running Snowcat .::.")
    dumpToJson(tlaModule, "pre")

    val tool = new TypeCheckerTool(annotationStore, inferPoly)

    // when this flag is true by the end of type checking, we have recovered the types of all expressions
    var isTypeCoverageComplete = true

    def defaultTag(uid: UID): TypeTag = {
      isTypeCoverageComplete = false
      val locStr = findLoc(uid)
      val msg = s"[$locStr]: Failed to recover the expression type for uid=$uid. You may see an error later."
      logger.error(msg)
      Untyped()
    }

    val listener = new LoggingTypeCheckerListener(sourceStore, changeListener, inferPoly)
    val taggedModule = tool.checkAndTag(tracker, listener, defaultTag, tlaModule)

    taggedModule match {
      case Some(newModule) =>
        logger.info(" > Your types are purrfect!")
        logger.info(if (isTypeCoverageComplete) " > All expressions are typed" else " > Some expressions are untyped")
        dumpToJson(newModule, "post")
        writerFactory
          .writeModuleAllFormats(newModule.copy(name = s"${passNumber}_Out$name"), TlaWriter.STANDARD_MODULES)

        utils.writeToOutput(newModule, options, writerFactory, logger, sourceStore)

        Some(newModule)
      case None =>
        logger.info(" > Snowcat asks you to fix the types. Meow.")
        None
    }
  }

  private def dumpToJson(module: TlaModule, prefix: String): Unit = {
    val fname = s"${passNumber}_out-$prefix-$name.json"
    OutputManager.withWriterInIntermediateDir(fname) { writer =>
      val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)
      val jsonText = new TlaToUJson(Some(sourceLocator)).makeRoot(Seq(module)).toString
      writer.write(jsonText)
      logger.debug(s" > JSON output: $fname")
    }
  }

  private def findLoc(id: UID): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(id) match {
      case Some(loc) => loc.toString
      case None      => "<unknown location>"
    }
  }

  override def dependencies = Set()

  override def transformations = Set(ModuleProperty.TypeChecked)
}
