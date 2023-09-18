package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.formulas.{BoolSort, Term, Variable}

/**
 * VMTExpr objects are wrappers around SMT Terms. They exist to let the writer to the output file know which labels to
 * add to which SMT expression.
 *
 * @author
 *   Jure Kukovec
 */
abstract class VMTExpr

sealed case class Next(name: String, current: Variable, next: Variable) extends VMTExpr {
  require(current.sort == next.sort, s"Variable binding $name must bind two variables of the same sort.")
}
sealed case class Init(name: String, initExpr: Term) extends VMTExpr {
  require(initExpr.sort == BoolSort, s"Initial state predicate $name must have Boolean sort.")
}
sealed case class Trans(name: String, transExpr: Term) extends VMTExpr {
  require(transExpr.sort == BoolSort, s"Transition predicate $name must have Boolean sort.")
}
sealed case class Invar(name: String, idx: Int, invExpr: Term) extends VMTExpr {
  require(invExpr.sort == BoolSort, s"Invariant $name must have Boolean sort.")
}
