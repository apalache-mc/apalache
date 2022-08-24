package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.ExitCodes
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.infra.passes.PassOptions
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.lir.TlaWriterFactory
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.imp.utils
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.TypeCheckerTool
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

class EtcTypeCheckerPassImpl @Inject() (
    val options: PassOptions,
    val sourceStore: SourceStore,
    changeListener: ChangeListener,
    tracker: TransformationTracker,
    val annotationStore: AnnotationStore,
    val writerFactory: TlaWriterFactory)
    extends EtcTypeCheckerPass with LazyLogging {

  protected def inferPoly: Boolean = options.getOrElse[Boolean]("typecheck", "inferPoly", true)

  // use rows by default, unless the user passed --features=no-rows
  protected def useRows: Boolean =
    !options.getOrElse[Seq[Feature]]("general", "features", Seq()).contains(ImpreciseRecordsFeature())

  override def name: String = "TypeCheckerSnowcat"

  override def execute(tlaModule: TlaModule): PassResult = {
    logger.info(" > Running Snowcat .::.")

    val tool = new TypeCheckerTool(annotationStore, inferPoly, useRows)

    // when this flag is true by the end of type checking, we have recovered the types of all expressions
    var isTypeCoverageComplete = true

    def defaultTag(uid: UID): TypeTag = {
      isTypeCoverageComplete = false
      val locStr = findLoc(uid)
      val msg = s"[$locStr]: Failed to recover the expression type for uid=$uid. You may see an error later."
      logger.error(msg)
      Untyped
    }

    val listener = new LoggingTypeCheckerListener(sourceStore, changeListener, inferPoly)
    val taggedModule = tool.checkAndTag(tracker, listener, defaultTag, tlaModule)

    taggedModule match {
      case Some(newModule) =>
        logger.info(" > Your types are purrfect!")
        logger.info(if (isTypeCoverageComplete) " > All expressions are typed" else " > Some expressions are untyped")
        writeOut(writerFactory, newModule)

        utils.writeToOutput(newModule, options, writerFactory, logger, sourceStore)

        Right(newModule)
      case None =>
        logger.info(" > Snowcat asks you to fix the types. Meow.")
        Left(ExitCodes.ERROR_TYPECHECK)
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
