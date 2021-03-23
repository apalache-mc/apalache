package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.TlaType1
import at.forsyte.apalache.tla.typecheck.etc.{EtcRef, ExactRef}

/**
 * <p>Type checker calls the listener on important events:</p>
 *
 * <ol>
 *  <li>the type of a new expression has been computed, or </li>
 *  <li>a type error has been found.</li>
 * </ol>
 *
 * @author Igor Konnov
 */
trait TypeCheckerListener {

  /**
   * This method is called when the type checker finds the type of an expression.
   * @param sourceRef a reference to the source expression; this reference must be exact
   * @param monotype its monotype
   */
  def onTypeFound(sourceRef: ExactRef, monotype: TlaType1)

  /**
   * This method is called when the type checker finds a type error.
   * @param sourceRef a reference to the source expression; this one does not have to be exact
   * @param message the error description
   */
  def onTypeError(sourceRef: EtcRef, message: String)
}
