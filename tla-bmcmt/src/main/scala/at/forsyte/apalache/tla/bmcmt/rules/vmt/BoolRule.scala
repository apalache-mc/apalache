package at.forsyte.apalache.tla.bmcmt.rules.vmt
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas.Term
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

/**
 * BoolRule defines translations for reTLA patterns which use operators from propositional logic.
 *
 * @author
 *   Jure Kukovec
 */
class BoolRule(rewriter: Rewriter) extends FormulaRule {
  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.not | TlaBoolOper.implies | TlaBoolOper.equiv, _*) =>
        true
      case _ => false
    }

  // convenience shorthand
  private def rewrite: TlaEx => Term = rewriter.rewrite

  // Assume isApplicable
  override def apply(ex: TlaEx): BoolExpr =
    ex match {
      case OperEx(TlaBoolOper.and, args @ _*)    => And(args.map(rewrite): _*)
      case OperEx(TlaBoolOper.or, args @ _*)     => Or(args.map(rewrite): _*)
      case OperEx(TlaBoolOper.not, arg)          => Neg(rewrite(arg))
      case OperEx(TlaBoolOper.implies, lhs, rhs) => Impl(rewrite(lhs), rewrite(rhs))
      case OperEx(TlaBoolOper.equiv, lhs, rhs)   => Equiv(rewrite(lhs), rewrite(rhs))
      case _                                     => throw new RewriterException(s"BoolRule not applicable to $ex", ex)
    }
}
