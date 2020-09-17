package at.forsyte.apalache.tla.typecheck

/**
  * The interface to a type checker.
  *
  * @author Igor Konnov
  */
trait TypeChecker {
  /**
    * Compute the expression type in a type context. If the expression is not well-typed, return None.
    * As a side effect, call the listener, when discovering new types or errors.
    *
    * @param listener a listener that will receive the type error or type info
    * @param ctx a typing context
    * @param ex an expression
    * @return Some(type), if the expression is well-typed; and None otherwise.
    */
  def compute(listener: TypeCheckerListener, ctx: TypeContext, ex: STCExpr): Option[TlaType1]
}
