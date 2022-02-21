package at.forsyte.apalache.tla.lir.formulas

import at.forsyte.apalache.tla.lir.formulas.StandardSorts.{FunctionSort, UninterpretedSort}

object EUF {

  import Booleans.BoolExpr

  sealed case class UninterpretedLiteral(s: String, sort: UninterpretedSort) extends Term
  sealed case class UninterpretedVar(name: String, sort: UninterpretedSort) extends Variable(name)
  sealed case class Equal(lhs: Term, rhs: Term) extends BoolExpr {
    require(lhs.sort == rhs.sort)
  }
  sealed case class ITE(cond: BoolExpr, thenTerm: Term, elseTerm: Term) extends Term {
    require(thenTerm.sort == elseTerm.sort)
    val sort: Sort = thenTerm.sort
  }

  sealed case class FunDef(name: String, args: List[(String, Sort)], body: Term) extends FnTerm {
    val sort: FunctionSort = FunctionSort(body.sort, args map { _._2 }: _*)
  }
  sealed case class FunctionVar(name: String, sort: FunctionSort) extends Variable(name) with FnTerm
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
