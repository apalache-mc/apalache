package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{TlaType1, TypingException, UID}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.typecheck.{TypeCheckerListener, TypingInputException}
import at.forsyte.apalache.tla.typecheck.etc.{EtcRef, ExactRef}
import com.typesafe.scalalogging.LazyLogging

class LoggingTypeCheckerListener(sourceStore: SourceStore, changeListener: ChangeListener,
    isPolymorphismEnabled: Boolean)
    extends TypeCheckerListener with LazyLogging {

  /**
   * This method is called when the type checker finds the type of an expression.
   *
   * @param sourceRef a reference to the source expression; this reference must be exact
   * @param tp        its type
   */
  override def onTypeFound(sourceRef: ExactRef, tp: TlaType1): Unit = {
    if (!isPolymorphismEnabled && tp.usedNames.nonEmpty) {
      val msg = "[%s]: Found a polymorphic type: %s".format(findLoc(sourceRef.tlaId), tp)
      logger.error(msg)
      logger.error("Probable causes: an empty set { } needs a type annotation or an incorrect record field is used")
      throw new TypingInputException(msg)
    }
  }

  /**
   * This method is called when the type checker finds a type error.
   *
   * @param sourceRef a reference to the source expression; this one does not have to be exact
   * @param message   the error description
   */
  override def onTypeError(sourceRef: EtcRef, message: String): Unit = {
    logger.error("[%s]: %s".format(findLoc(sourceRef.tlaId), message))
  }

  private def findLoc(id: UID): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(id) match {
      case Some(loc) => loc.toString
      case None      => "unknown location"
    }
  }
}
