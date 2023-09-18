package at.forsyte.apalache.tla.lir.formulas

object Integers {

  trait IntExpr extends Term {
    val sort: Sort = IntSort
  }

  sealed case class Plus(lhs: Term, rhs: Term) extends IntExpr {
    require(Seq(lhs, rhs).forall { _.sort == IntSort }, "Plus is only applicable to arguments with Integer sorts.")
  }
  sealed case class Minus(lhs: Term, rhs: Term) extends IntExpr {
    require(Seq(lhs, rhs).forall { _.sort == IntSort }, "Minus is only applicable to arguments with Integer sorts.")
  }
  sealed case class Uminus(arg: Term) extends IntExpr {
    require(arg.sort == IntSort, "Uminus is only applicable to arguments with Integer sorts.")
  }
  sealed case class Mult(lhs: Term, rhs: Term) extends IntExpr {
    require(Seq(lhs, rhs).forall { _.sort == IntSort }, "Mult is only applicable to arguments with Integer sorts.")
  }
  sealed case class Div(lhs: Term, rhs: Term) extends IntExpr {
    require(Seq(lhs, rhs).forall { _.sort == IntSort }, "Div is only applicable to arguments with Integer sorts.")
  }
  sealed case class Mod(lhs: Term, rhs: Term) extends IntExpr {
    require(Seq(lhs, rhs).forall { _.sort == IntSort }, "Mod is only applicable to arguments with Integer sorts.")
  }
  sealed case class Abs(arg: Term) extends IntExpr {
    require(arg.sort == IntSort, "Abs is only applicable to arguments with Integer sorts.")
  }

  sealed case class Lt(lhs: Term, rhs: Term) extends Booleans.BoolExpr {
    require(Seq(lhs, rhs).forall { _.sort == IntSort }, "[<] is only applicable to arguments with Integer sorts.")
  }
  sealed case class Le(lhs: Term, rhs: Term) extends Booleans.BoolExpr {
    require(Seq(lhs, rhs).forall { _.sort == IntSort }, "[<=] is only applicable to arguments with Integer sorts.")
  }
  sealed case class Gt(lhs: Term, rhs: Term) extends Booleans.BoolExpr {
    require(Seq(lhs, rhs).forall { _.sort == IntSort }, "[>] is only applicable to arguments with Integer sorts.")
  }
  sealed case class Ge(lhs: Term, rhs: Term) extends Booleans.BoolExpr {
    require(Seq(lhs, rhs).forall { _.sort == IntSort }, "[>=] is only applicable to arguments with Integer sorts.")
  }

  sealed case class IntLiteral(i: BigInt) extends IntExpr
  sealed case class IntVar(name: String) extends Variable(name) with IntExpr
}
