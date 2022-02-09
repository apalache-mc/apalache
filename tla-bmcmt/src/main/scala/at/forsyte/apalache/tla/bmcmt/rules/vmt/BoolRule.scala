package at.forsyte.apalache.tla.bmcmt.rules.vmt
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.formulas.{StandardSorts, Term}
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

class BoolRule(rewriter: BoolRewriter) extends BoolTermRule {
  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.not | TlaBoolOper.implies | TlaBoolOper.equiv, _*) =>
        true
      case _ => false
    }

  // Assume isApplicable
  override def apply(ex: TlaEx): Term[StandardSorts.BoolSort] =
    ex match {
      case OperEx(TlaBoolOper.and, args @ _*)    => And(args map rewriter.rewrite: _*)
      case OperEx(TlaBoolOper.or, args @ _*)     => Or(args map rewriter.rewrite: _*)
      case OperEx(TlaBoolOper.not, arg)          => Neg(rewriter.rewrite(arg))
      case OperEx(TlaBoolOper.implies, lhs, rhs) => Impl(rewriter.rewrite(lhs), rewriter.rewrite(rhs))
      case OperEx(TlaBoolOper.equiv, lhs, rhs)   => Equiv(rewriter.rewrite(lhs), rewriter.rewrite(rhs))
      case _                                     => throw new RewriterException(s"BoolRule not applicable to $ex", ex)
    }
}
