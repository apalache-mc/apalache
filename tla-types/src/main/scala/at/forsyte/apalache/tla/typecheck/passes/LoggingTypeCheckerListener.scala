package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.typecheck.{TlaType1, TypeCheckerListener}
import at.forsyte.apalache.tla.typecheck.etc.{EtcRef, ExactRef}
import com.typesafe.scalalogging.LazyLogging

class LoggingTypeCheckerListener(sourceStore: SourceStore)
    extends TypeCheckerListener
    with LazyLogging {

  /**
    * This method is called when the type checker finds the type of an expression.
    *
    * @param sourceRef a reference to the source expression; this reference must be exact
    * @param monotype  its monotype
    */
  override def onTypeFound(sourceRef: ExactRef, monotype: TlaType1): Unit = {}

  /**
    * This method is called when the type checker finds a type error.
    *
    * @param sourceRef a reference to the source expression; this one does not have to be exact
    * @param message   the error description
    */
  override def onTypeError(sourceRef: EtcRef, message: String): Unit = {
    val locStr = sourceStore
      .find(sourceRef.tlaId)
      .map(_.toString)
      .getOrElse("Unknown location")
    logger.error("[%s]: %s".format(locStr, message))
  }
}
