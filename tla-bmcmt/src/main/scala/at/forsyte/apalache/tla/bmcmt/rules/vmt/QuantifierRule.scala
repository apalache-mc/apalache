package at.forsyte.apalache.tla.bmcmt.rules.vmt
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.{BoolExpr, Exists, Forall}
import at.forsyte.apalache.tla.lir.formulas.Term
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

/**
 * QuantifierRule defines translations for quantified expressions in reTLA.
 *
 * `restrictedSetJudgement` determines which sets (by name) are considered restricted (and what their sorts are).
 *
 * @author
 *   Jure Kukovec
 */
class QuantifierRule(rewriter: ToTermRewriter, restrictedSetJudgement: RestrictedSetJudgement) extends FormulaRule {
  override def isApplicable(ex: TlaEx): Boolean = ex match {
    case OperEx(TlaBoolOper.exists | TlaBoolOper.forall, _, set, _) if isRestrictedSet(set) => true
    case _                                                                                  => false
  }

  private def isRestrictedSet(ex: TlaEx) = restrictedSetJudgement.isRestrictedSet(ex)

  // Convenience shorthand
  private def rewrite: TlaEx => Term = rewriter.rewrite

  // No magic here, all quantifiers in reTLA have fixed arity and are 1-to-1 with SMT quantifiers
  override def apply(ex: TlaEx): BoolExpr =
    ex match {
      case OperEx(TlaBoolOper.exists, NameEx(name), set, pred) if isRestrictedSet(set) =>
        Exists(List((name, restrictedSetJudgement.getSort(set))), rewrite(pred))
      case OperEx(TlaBoolOper.forall, NameEx(name), set, pred) if isRestrictedSet(set) =>
        Forall(List((name, restrictedSetJudgement.getSort(set))), rewrite(pred))
      case _ =>
        throw new RewriterException(s"QuantifierRule not applicable to $ex", ex)
    }

}
