package at.forsyte.apalache.tla.bmcmt.rules.vmt
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.{Exists, Forall}
import at.forsyte.apalache.tla.lir.formulas.{Sort, Term}
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

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
  private def rewrite: TlaEx => TermBuilderT = rewriter.rewrite

  // Both \E and \A translate the same, up to the constructor name
  private def mk(Ctor: (Seq[(String, Sort)], Term) => Term)(name: String, set: TlaEx, pred: TlaEx): TermBuilderT = {
    val setSort = restrictedSetJudgement.getSort(set)
    for {
      _ <- storeUninterpretedSort(setSort)
      predTerm <- rewrite(pred)
    } yield Ctor(Seq((name, setSort)), predTerm)
  }

  // No magic here, all quantifiers in reTLA have fixed arity and are 1-to-1 with SMT quantifiers
  override def apply(ex: TlaEx): TermBuilderT =
    ex match {
      case OperEx(TlaBoolOper.exists, NameEx(name), set, pred) if isRestrictedSet(set) =>
        mk(Exists)(name, set, pred)
      case OperEx(TlaBoolOper.forall, NameEx(name), set, pred) if isRestrictedSet(set) =>
        mk(Forall)(name, set, pred)
      case _ =>
        throw new RewriterException(s"QuantifierRule not applicable to $ex", ex)
    }

}
