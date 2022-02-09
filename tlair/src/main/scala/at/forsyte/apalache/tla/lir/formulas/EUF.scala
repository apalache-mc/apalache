package at.forsyte.apalache.tla.lir.formulas

object EUF {

  import Booleans.BoolExpr

  sealed case class Equal[S <: Sort](lhs: Term[S], rhs: Term[S]) extends BoolExpr
  sealed case class ITE[S <: Sort](cond: BoolExpr, lhs: Term[S], rhs: Term[S]) extends Term[S]
  sealed case class Apply[S <: Sort](fn: Function[S], args: AbstractTerm*) extends Term[S] {
    require(isValid)
    private def isValid: Boolean =
      if (args.size != fn.from.size) false
      else {
        args.zip(fn.from).forall { case (arg, param) =>
          arg.isInstanceOf[Term[param.type]]
        }
      }
  }
}
