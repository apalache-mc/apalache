package at.forsyte.apalache.tla.lir.formulas

import at.forsyte.apalache.tla.lir.formulas.StandardSorts.FunctionSort

object EUF {

  import Booleans.BoolExpr

  sealed case class UninterpretedLiteral(s: String, sort: Sort) extends Term
  sealed case class UninterpretedVar(name: String, sort: Sort) extends Variable(name)
  sealed case class Equal(lhs: Term, rhs: Term) extends BoolExpr {
    require(lhs.sort == rhs.sort)
  }
  sealed case class ITE(cond: BoolExpr, lhs: Term, rhs: Term) extends Term {
    require(lhs.sort == rhs.sort)
    val sort: Sort = lhs.sort
  }

//  sealed case class UninterpretedFunLiteral(s: String, sort: FunctionSort) extends FnTerm
  sealed case class UninterpretedFunVar(name: String, sort: FunctionSort) extends Variable(name) with FnTerm
  sealed case class Apply(fn: FnTerm, args: Term*) extends Term {
    require(isValid)
    private def isValid: Boolean =
      if (args.size != fn.sort.from.size) false
      else {
        args.zip(fn.sort.from).forall { case (arg, expectedSort) =>
          arg.sort == expectedSort
        }
      }
    val sort: Sort = fn.sort.to
  }
}
