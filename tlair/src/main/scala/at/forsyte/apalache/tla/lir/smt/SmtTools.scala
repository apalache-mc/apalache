package at.forsyte.apalache.tla.lir.smt

object SmtTools {

  abstract class BoolFormula

  sealed case class False() extends BoolFormula

  sealed case class And(args: BoolFormula*) extends BoolFormula

  sealed case class Or(args: BoolFormula*) extends BoolFormula

  sealed case class Neg(arg: BoolFormula) extends BoolFormula

  sealed case class Implies(LHS: BoolFormula, RHS: BoolFormula) extends BoolFormula

  sealed case class Variable(id: Long) extends BoolFormula

  // ( R( i ) < R( j ) )
  sealed case class LtFns(i: Long, j: Long) extends BoolFormula
  // ( R( i ) != R( j ) )
  sealed case class NeFns(i: Long, j: Long) extends BoolFormula

  /**
   * Converts a BoolFormula to an smt2 string
   * @param phi Input formula
   * @return SMT encoding of the boolean formula
   */
  def toSmt2(phi: BoolFormula, varSym: String = "b", fnSym: String = "R"): String = {
    val self: BoolFormula => String = toSmt2(_, varSym, fnSym)
    phi match {
      case False() =>
        "false"
      case And(args @ _*) =>
        "( and %s )".format(args.map(self).mkString(" "))
      case Or(args @ _*) =>
        "( or %s )".format(args.map(self).mkString(" "))
      case Neg(arg: BoolFormula) =>
        "( not %s )".format(toSmt2(arg))
      case Implies(lhs, rhs) =>
        "( => %s %s )".format(toSmt2(lhs), toSmt2(rhs))
      case Variable(id: Long) =>
        "%s_%s".format(varSym, id)
      case LtFns(i: Long, j: Long) =>
        "( < ( %s %s ) ( %s %s ) )".format(fnSym, i, fnSym, j)
      case NeFns(i: Long, j: Long) =>
        "( not ( = ( %s %s ) ( %s %s ) ) )".format(fnSym, i, fnSym, j)
    }
  }

  /**
   * Removes redundant connectives.
   * @param phi Input formula
   * @return Logically equivalent subset formula.
   */
  def simplify(phi: BoolFormula): BoolFormula = {
    phi match {
      /**
       * Recursively simplify branches first.
       * If any branch is false, the whole formula is false.
       * It is important to recurse first,
       * since otherwise false-simplification would not propagate upward.
       */
      case And(args @ _*) =>
        val newargs = args.map(simplify)
        if (newargs.contains(False()))
          False()
        else
          And(newargs: _*)

      /**
       * Recursively simplify, then drop all False() branches.
       * Afterwards, if the new tree has too few branches prune accordingly.
       */
      case Or(args @ _*) =>
        val newargs = args.map(simplify).filterNot(_ == False())
        newargs.size match {
          case 0 =>
            False()
          case 1 =>
            newargs.head
          case _ =>
            Or(newargs: _*)
        }

      case _ =>
        phi
    }
  }

}
