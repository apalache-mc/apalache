package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.passes.{Pass, PassOptions, TlaModuleMixin}
import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.typecheck.TypeCheckerTool
import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

class EtcTypeCheckerPassImpl @Inject() (val options: PassOptions, val sourceStore: SourceStore,
    val annotationStore: AnnotationStore, @Named("AfterTypeChecker") val nextPass: Pass with TlaModuleMixin)
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
      val isWellDefined = tool.check(new LoggingTypeCheckerListener(sourceStore), tlaModule.get)
      logger.info(if (isWellDefined) " > Your types are great!" else " > Snowcat asks you to fix the types. Meow.")
      isWellDefined
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
