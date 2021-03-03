package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.{TypeTag, UID, Untyped}
import at.forsyte.apalache.tla.typecheck.TypeCheckerTool
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class EtcTypeCheckerPassImpl @Inject() (val options: PassOptions, val sourceStore: SourceStore,
    tracker: TransformationTracker, val annotationStore: AnnotationStore,
    @Named("AfterTypeChecker") val nextPass: Pass with TlaModuleMixin)
    extends EtcTypeCheckerPass with LazyLogging {

  /**
   * The name of the pass
   *
   * @return the name associated with the pass
   */
  override def name: String = "TypeChecker"

  /**
   * Run the pass.
   *
   * @return true, if the pass was successful
   */
  override def execute(): Boolean = {
    if (tlaModule.isDefined) {
      logger.info(" > Running Snowcat .::.")
      val inferPoly = options.getOrElse("typecheck", "inferPoly", true)
      val tool = new TypeCheckerTool(annotationStore, inferPoly)

      def defaultTag(uid: UID): TypeTag = {
        val locStr = sourceStore.find(uid).map(_.toString).getOrElse("Unknown location")
        val msg = s"[$locStr]: Failed to recover the expression type for uid=$uid. You may see an error later."
        logger.error(msg)
        Untyped()
      }

      val listener = new LoggingTypeCheckerListener(sourceStore)
      val taggedModule = tool.checkAndTag(tracker, listener, defaultTag, tlaModule.get)

      taggedModule match {
        case Some(_) =>
          logger.info(" > Your types are great!")
          // TODO: output the module in the json format, once the PR #599 has been merged
          true

        case None =>
          logger.info(" > Snowcat asks you to fix the types. Meow.")
          false
      }
    } else {
      logger.info(" > no input for type checker")
      false
    }
  }

  /**
   * Get the next pass in the chain. What is the next pass is up
   * to the module configuration and the pass outcome.
   *
   * @return the next pass, if exists, or None otherwise
   */
  override def next(): Option[Pass] =
    tlaModule map { _ => nextPass }
}
