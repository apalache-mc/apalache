package at.forsyte.apalache.tla.passes.typecheck

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.TlaType1
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.etc._
import com.typesafe.scalalogging.LazyLogging

class LoggingTypeCheckerListener(
    sourceStore: SourceStore,
    changeListener: ChangeListener,
    isPolymorphismEnabled: Boolean)
    extends SourceAwareTypeCheckerListener(sourceStore, changeListener) with LazyLogging {

  /**
   * This method is called when the type checker finds the type of an expression.
   *
   * @param sourceRef
   *   a reference to the source expression; this reference must be exact
   * @param tp
   *   its type
   */
  override def onTypeFound(sourceRef: ExactRef, tp: TlaType1): Unit = {
    if (!isPolymorphismEnabled && tp.usedNames.nonEmpty) {
      val msg = s"Found a polymorphic type: $tp"
      logger.error(msg)
      logger.error("Probable causes: an empty set { } needs a type annotation or an incorrect record field is used")
      throw new TypingInputException(msg, sourceRef.tlaId)
    }
  }

  /**
   * This method is called when the type checker finds a type error.
   *
   * @param sourceRef
   *   a reference to the source expression; this one does not have to be exact
   * @param message
   *   the error description
   */
  override def onTypeError(sourceRef: EtcRef, message: String): Unit = {
    logger.error("[%s]: %s".format(findLoc(sourceRef.tlaId), message))
  }

  /**
   * This method is called when the type checker finds a type warning.
   *
   * @param sourceRef
   *   a reference to the source expression; this one does not have to be exact
   * @param message
   *   the warning description
   */
  override def onTypeWarn(sourceRef: EtcRef, message: String): Unit = {
    logger.debug("[%s]: %s".format(findLoc(sourceRef.tlaId), message))
  }
}
