package at.forsyte.apalache.tla.lir.formulas

/**
 * EUF defines constructors for terms in the fragment of (E)quality and (U)ninterpreted (f)unctions.
 *
 * @author
 *   Jure Kukovec
 */
object EUF {

  import Booleans.BoolExpr

  sealed case class UninterpretedLiteral(s: String, sort: UninterpretedSort) extends Term
  sealed case class UninterpretedVar(name: String, sort: UninterpretedSort) extends Variable(name)
  sealed case class Equal(lhs: Term, rhs: Term) extends BoolExpr {
    // Sanity check
    require(lhs.sort == rhs.sort, "Equality is only defined for terms of matching sorts.")
  }
  sealed case class ITE(cond: BoolExpr, thenTerm: Term, elseTerm: Term) extends Term {
    // Sanity check
    require(thenTerm.sort == elseTerm.sort, "ITE is only defined for branches of matching sorts")
    val sort: Sort = thenTerm.sort
  }

  /**
   * A function term. FunDef plays a dual role, because it conceptually represents side-effects: SMT requires that each
   * function is defined separately from where it is used, unlike TLA. If we want to translate a TLA syntax-tree to
   * s-expressions, we either need side-effects (for introducing definitions), or as is the case with FunDef, we pack
   * the definition with the term, and recover it later (see VMTWriter::Collector)
   *
   * In terms of s-expressions (and when translated to a string), it is equivalent to FunctionVar(name, sort).
   */
  sealed case class FunDef(name: String, args: List[(String, Sort)], body: Term) extends FnTerm {
    val sort: FunctionSort = FunctionSort(body.sort, args.map { _._2 }: _*)
  }
  sealed case class FunctionVar(name: String, sort: FunctionSort) extends Variable(name) with FnTerm
  sealed case class Apply(fn: FnTerm, args: Term*) extends Term {
    // Apply is valid, if fn has a function sort (S1, ..., Sn) -> S
    // and args have sorts S1, ..., Sn. Then, Apply has sort S
    require(isValid, "Apply is only defined when the sorts of the arguments fit the function's FunctionSort")
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
