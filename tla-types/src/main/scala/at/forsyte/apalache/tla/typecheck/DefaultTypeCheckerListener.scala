package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.typecheck.etc.{EtcRef, ExactRef}

/**
  * The default implementation of TypeCheckerListener that does nothing.
  *
  * @author Igor Konnov
  */
class DefaultTypeCheckerListener extends TypeCheckerListener {

  /**
    * This method is called when the type checker finds the type of an expression.
    *
    * @param sourceRef an exact reference to the source expression
    * @param monotype its monotype
    */
  override def onTypeFound(sourceRef: ExactRef, monotype: TlaType1): Unit = {}

  /**
    * This method is called when the type checker finds a type error.
    *
    * @param sourceRef a reference to the source expression
    * @param message the error description
    */
  override def onTypeError(sourceRef: EtcRef, message: String): Unit = {}
}
