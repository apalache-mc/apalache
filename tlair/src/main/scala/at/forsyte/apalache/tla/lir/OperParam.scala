package at.forsyte.apalache.tla.lir

/**
 * A formal parameter of an operator. A parameter is either: a value (`arity = 0`), or an operator (`arity > 0`).
 * Higher-order operators have at least one parameter that is an operator itself.
 * We declare `OperParam` as a case class, in order to have `equals`
 * and pattern-matching.
 */
case class OperParam(val name: String, val arity: Int) extends Serializable {

  /**
   * Is the parameter an operator.
   *
   * @return true, if the parameter is an operator
   */
  def isOperator: Boolean = arity > 0
}

object OperParam {
  def apply(name: String): OperParam = {
    OperParam(name, 0)
  }
}
