package at.forsyte.apalache.tla.lir.formulas

import at.forsyte.apalache.tla.lir.formulas.StandardSorts.BoolSort

object Booleans {
  trait BoolExpr extends Term {
    val sort: Sort = BoolSort()
  }

  object False extends BoolExpr
  object True extends BoolExpr
  sealed case class And(args: BoolExpr*) extends BoolExpr
  sealed case class Or(args: BoolExpr*) extends BoolExpr
  sealed case class Neg(arg: BoolExpr) extends BoolExpr
  sealed case class Impl(lhs: BoolExpr, rhs: BoolExpr) extends BoolExpr
  sealed case class Equiv(lhs: BoolExpr, rhs: BoolExpr) extends BoolExpr
  sealed case class Forall(name: String, ofSort: Sort, arg: BoolExpr) extends BoolExpr
  sealed case class Exists(name: String, ofSort: Sort, arg: BoolExpr) extends BoolExpr
  sealed case class BoolVar(name: String) extends Variable(name) with BoolExpr
}
