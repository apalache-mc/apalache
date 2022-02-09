package at.forsyte.apalache.tla.lir.formulas

object Integers {

  type IntExpr = Term[StandardSorts.IntSort]

  sealed case class Plus(lhs: IntExpr, rhs: IntExpr) extends IntExpr
  sealed case class Minus(lhs: IntExpr, rhs: IntExpr) extends IntExpr
  sealed case class Uminus(arg: IntExpr) extends IntExpr
  sealed case class Mult(lhs: IntExpr, rhs: IntExpr) extends IntExpr
  sealed case class Div(lhs: IntExpr, rhs: IntExpr) extends IntExpr
  sealed case class Mod(lhs: IntExpr, rhs: IntExpr) extends IntExpr
  sealed case class Abs(arg: IntExpr) extends IntExpr

  sealed case class Lt(lhs: IntExpr, rhs: IntExpr) extends Booleans.BoolExpr
  sealed case class Le(lhs: IntExpr, rhs: IntExpr) extends Booleans.BoolExpr
  sealed case class Gt(lhs: IntExpr, rhs: IntExpr) extends Booleans.BoolExpr
  sealed case class Ge(lhs: IntExpr, rhs: IntExpr) extends Booleans.BoolExpr

  sealed case class IntVar(name: String) extends Variable[StandardSorts.IntSort](name) with IntExpr
}
