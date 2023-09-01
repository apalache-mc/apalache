package at.forsyte.apalache.tla.bmcmt.rules.vmt
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
 * BoolRule defines translations for reTLA patterns which use operators from propositional logic.
 *
 * @author
 *   Jure Kukovec
 */
class BoolRule(rewriter: ToTermRewriter) extends FormulaRule {
  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.not | TlaBoolOper.implies | TlaBoolOper.equiv, _*) =>
        true
      case _ => false
    }

  // convenience shorthand
  private def rewrite: TlaEx => TermBuilderT = rewriter.rewrite

  // Assume isApplicable
  override def apply(ex: TlaEx): TermBuilderT =
    ex match {
      case OperEx(TlaBoolOper.and, args @ _*) => cmpSeq(args.map(rewrite)).map { seq => And(seq: _*) }
      case OperEx(TlaBoolOper.or, args @ _*)  => cmpSeq(args.map(rewrite)).map { seq => Or(seq: _*) }
      case OperEx(TlaBoolOper.not, arg)       => rewrite(arg).map(Neg)
      case OperEx(TlaBoolOper.implies, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Impl(lhsTerm, rhsTerm)
      case OperEx(TlaBoolOper.equiv, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Equiv(lhsTerm, rhsTerm)
      case _ => throw new RewriterException(s"BoolRule not applicable to $ex", ex)
    }
}
