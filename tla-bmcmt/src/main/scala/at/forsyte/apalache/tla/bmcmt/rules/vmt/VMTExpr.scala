package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.formulas.Booleans.BoolExpr
import at.forsyte.apalache.tla.lir.formulas.Variable

abstract class VMTExpr

sealed case class Next(name: String, current: Variable, next: Variable) extends VMTExpr {
  require(current.sort == next.sort)
}
sealed case class Init(name: String, initExpr: BoolExpr) extends VMTExpr
sealed case class Trans(name: String, transExpr: BoolExpr) extends VMTExpr
sealed case class Invar(name: String, idx: Int, invExpr: BoolExpr) extends VMTExpr
