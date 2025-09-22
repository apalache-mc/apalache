package at.forsyte.apalache.tla.typecheck.integration

import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{TlaType1, UID}
import at.forsyte.apalache.tla.typecheck._
import at.forsyte.apalache.tla.typecheck.etc._

import scala.collection.mutable

/**
 * This listener maintains a map of UIDs to types. The map can be used to assign types to expressions and declarations.
 * It can be also used to implement a language protocol.
 *
 * @author
 *   Igor Konnov
 */
class RecordingTypeCheckerListener(sourceStore: SourceStore, changeListener: ChangeListener)
    extends SourceAwareTypeCheckerListener(sourceStore, changeListener) {
  private val uidToType: mutable.Map[UID, TlaType1] = mutable.Map[UID, TlaType1]()

  def toMap: Map[UID, TlaType1] = {
    uidToType.toMap
  }

  private val _errors: mutable.ListBuffer[(String, String)] = mutable.ListBuffer.empty
  private val _warnings: mutable.ListBuffer[(String, String)] = mutable.ListBuffer.empty

  def getErrors(): List[(String, String)] = _errors.toList

  def getWarnings(): List[(String, String)] = _warnings.toList

  override def onTypeFound(sourceRef: ExactRef, monotype: TlaType1): Unit = {
    uidToType += sourceRef.tlaId -> monotype
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
    _errors += (findLoc(sourceRef.tlaId) -> message)
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
    _warnings += (findLoc(sourceRef.tlaId) -> message)
  }
}
