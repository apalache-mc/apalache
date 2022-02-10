package at.forsyte.apalache.tla.lir.formulas

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
  sealed case class Apply(fn: Function, args: Term*) extends Term {
    require(isValid)
    private def isValid: Boolean =
      if (args.size != fn.from.size) false
      else {
        args.zip(fn.from).forall { case (arg, expectedSort) =>
          arg.sort == expectedSort
        }
      }
    val sort: Sort = fn.to
  }
}
