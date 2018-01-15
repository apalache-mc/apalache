package at.forsyte.apalache.tla.bmcmt.analyses


/**
  * Similar to TLA+ level, we define grades, which are useful for caching model checking results:
  * <ol>
  * <li> a constant expression, i.e., referring only to constants and standard expressions,</li>
  * <li> an action-level expression that is referring only to constants and state variables,
  *      but not parameters or bound variables, e.g., x + 1 if x is a VARIABLE, but not y + 1,
  *      if y is a variable bound with \E y \in ...</li>
  * <li> an action-level expression that refers to bound variables and parameters, and</li>
  * <li> another expression of higher grade, e.g., a temporal level expression <>A.
  * </ol>
  *
  * @author Igor Konnov
  */
object ExprGrade extends Enumeration {
  val Constant, ActionFree, ActionBound, Higher = Value

  def join(left: Value, right: Value): Value = {
    (left, right) match {
      case (Higher, _) | (_, Higher) => Higher
      case (ActionBound, _) | (_, ActionBound) => ActionBound
      case (ActionFree, _) | (_, ActionFree) => ActionFree
      case _ => Constant
    }
  }
}
