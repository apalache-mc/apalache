package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.UID

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
    * @param id expression id
    * @param monotype its monotype
    */
  def onTypeFound(id: UID, monotype: TlaType1)

  /**
    * This method is called when the type checker finds a type error.
    * @param id expression id
    * @param message the error description
    */
  def onTypeError(id: UID, message: String)
}
