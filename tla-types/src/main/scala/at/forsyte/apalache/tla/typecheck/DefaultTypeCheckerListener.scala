package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.UID

/**
  * The default implementation of TypeCheckerListener that does nothing.
  *
  * @author Igor Konnov
  */
class DefaultTypeCheckerListener extends TypeCheckerListener {
  /**
    * This method is called when the type checker finds the type of an expression.
    *
    * @param id       expression id
    * @param monotype its monotype
    */
  override def onTypeFound(id: UID, monotype: TlaType1): Unit = {}

  /**
    * This method is called when the type checker finds a type error.
    *
    * @param id       expression id
    * @param message the error description
    */
  override def onTypeError(id: UID, message: String): Unit = {}
}
