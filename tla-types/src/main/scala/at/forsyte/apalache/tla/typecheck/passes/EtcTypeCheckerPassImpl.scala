package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.io.OutputManager.Names.IntermediateFoldername
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.io.lir.{TlaWriter, TlaWriterFactory}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.{TlaModule, TypeTag, UID, Untyped}
import at.forsyte.apalache.tla.typecheck.TypeCheckerTool
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs.printer
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.Path

class EtcTypeCheckerPassImpl @Inject() (val options: PassOptions, val sourceStore: SourceStore,
    changeListener: ChangeListener, tracker: TransformationTracker, val annotationStore: AnnotationStore,
    val writerFactory: TlaWriterFactory, @Named("AfterTypeChecker") val nextPass: Pass with TlaModuleMixin)
    extends EtcTypeCheckerPass with LazyLogging {

  private var outputTlaModule: Option[TlaModule] = None

  protected def inferPoly: Boolean = options.getOrElse("typecheck", "inferPoly", true)

  protected def passNumber: String = "01"

  /**
   * The name of the pass
   *
   * @return the name associated with the pass
   */
  override def name: String = "TypeCheckerSnowcat"

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    if (tlaModule.isEmpty) {
      logger.info(" > no input for type checker")
      false
    } else {
      logger.info(" > Running Snowcat .::.")
      dumpToJson(tlaModule.get, "pre")

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
      val taggedModule = tool.checkAndTag(tracker, listener, defaultTag, tlaModule.get)

      taggedModule match {
        case Some(newModule) =>
          logger.info(" > Your types are great!")
          logger.info(if (isTypeCoverageComplete) " > All expressions are typed" else " > Some expressions are untyped")
          dumpToJson(newModule, "post")
          writerFactory.writeModuleAllFormats(newModule.copy(name = s"${passNumber}_Out$name"),
              TlaWriter.STANDARD_MODULES)
          outputTlaModule = Some(newModule)
          true

        case None =>
          logger.info(" > Snowcat asks you to fix the types. Meow.")
          false
      }
    }
  }

  private def dumpToJson(module: TlaModule, prefix: String): Unit = {
    OutputManager.doIfFlag(OutputManager.Names.IntermediateFlag) {
      OutputManager.runDirPathOpt.foreach { runDir =>
        val outdir = new File(runDir.toFile, IntermediateFoldername)
        val outFile = new File(outdir, s"${passNumber}_out-$prefix-$name.json")
        val writer = new PrintWriter(new FileWriter(outFile, false))
        try {
          val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)
          val jsonText = new TlaToUJson(Some(sourceLocator)).makeRoot(Seq(module)).toString
          writer.write(jsonText)
          logger.debug(" > JSON output: " + outFile)
        } finally {
          writer.close()
        }
      }
    }
  }

  private def findLoc(id: UID): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(id) match {
      case Some(loc) => loc.toString
      case None      => "<unknown location>"
    }
  }

  /**
   * Get the next pass in the chain. What is the next pass is up
   * to the module configuration and the pass outcome.
   *
   * @return the next pass, if exists, or None otherwise
   */
  override def next(): Option[Pass] =
    outputTlaModule map { m =>
      nextPass.setModule(m)
      nextPass
    }
}
