package at.forsyte.apalache.tla.lir.formulas

/**
 * Booleans defines constructors for Boolean-sorted terms.
 *
 * @author
 *   Jure Kukovec
 */
object Booleans {
  trait BoolExpr extends Term {
    val sort: Sort = BoolSort
  }

  object False extends BoolExpr
  object True extends BoolExpr
  sealed case class And(args: Term*) extends BoolExpr {
    require(args.forall(_.sort == BoolSort), "All arguments of a conjunction must have Boolean sorts.")
  }
  sealed case class Or(args: Term*) extends BoolExpr {
    require(args.forall(_.sort == BoolSort), "All arguments of a disjunction must have Boolean sorts.")
  }
  sealed case class Neg(arg: Term) extends BoolExpr {
    require(arg.sort == BoolSort, "Negation is only applicable to arguments with Boolean sorts.")
  }
  sealed case class Impl(lhs: Term, rhs: Term) extends BoolExpr {
    require(Seq(lhs, rhs).forall { _.sort == BoolSort },
        "Implication is only applicable to arguments with Boolean sorts.")
  }
  sealed case class Equiv(lhs: Term, rhs: Term) extends BoolExpr {
    require(Seq(lhs, rhs).forall { _.sort == BoolSort },
        "Equivalence is only applicable to arguments with Boolean sorts.")
  }
  sealed case class Forall(boundVars: Seq[(String, Sort)], arg: Term) extends BoolExpr {
    require(arg.sort == BoolSort, "Quantification condition must be Boolean.")
  }
  sealed case class Exists(boundVars: Seq[(String, Sort)], arg: Term) extends BoolExpr {
    require(arg.sort == BoolSort, "Quantification condition must be Boolean.")
  }
  sealed case class BoolVar(name: String) extends Variable(name) with BoolExpr
}
