package at.forsyte.apalache.tla.bmcmt.rules.vmt
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.{Exists, Forall}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.formulas.{StandardSorts, Term}
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

class QuantifierRule(rewriter: BoolRewriter, restrictedSetJudgement: RestrictedSetJudgement) extends BoolTermRule {
  override def isApplicable(ex: TlaEx): Boolean = ex match {
    case OperEx(TlaBoolOper.exists | TlaBoolOper.forall, _, _, _) => true
    case _                                                        => false
  }

  private def isRestrictedSet(ex: TlaEx) = restrictedSetJudgement.isRestrictedSet(ex)

  override def apply(ex: TlaEx): Term[StandardSorts.BoolSort] =
    ex match {
      case OperEx(TlaBoolOper.exists, NameEx(name), set, pred) if isRestrictedSet(set) =>
        Exists(name, restrictedSetJudgement.getSort(set), rewriter.rewrite(pred))
      case OperEx(TlaBoolOper.forall, NameEx(name), set, pred) if isRestrictedSet(set) =>
        Forall(name, restrictedSetJudgement.getSort(set), rewriter.rewrite(pred))
      case _ =>
        throw new RewriterException(s"QuantifierRule not applicable to $ex", ex)
    }

}
