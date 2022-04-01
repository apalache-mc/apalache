package at.forsyte.apalache.tla.bmcmt.rules.vmt
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.{BoolExpr, Exists, Forall}
import at.forsyte.apalache.tla.lir.formulas.Term
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaBoolOper}

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
    case OperEx(ApalacheOper.`skolem`, OperEx(TlaBoolOper.exists, _: NameEx, set, _))
        if restrictedSetJudgement.isRestrictedSet(set) =>
      true
    case OperEx(TlaBoolOper.exists | TlaBoolOper.forall, _: NameEx, set, _)
        if restrictedSetJudgement.isPrimitiveRestrictedSet(set) =>
      true
    case _ => false
  }

  // Convenience shorthand
  private def rewrite: TlaEx => Term = rewriter.rewrite

  // No magic here, all quantifiers in reTLA have fixed arity and are 1-to-1 with SMT quantifiers
  override def apply(ex: TlaEx): Term =
    ex match {
      case OperEx(TlaBoolOper.exists, NameEx(name), set, pred)
          if restrictedSetJudgement.isPrimitiveRestrictedSet(set) =>
        Exists(List((name, restrictedSetJudgement.getSort(set))), rewrite(pred))
      case OperEx(TlaBoolOper.forall, NameEx(name), set, pred)
          if restrictedSetJudgement.isPrimitiveRestrictedSet(set) =>
        Forall(List((name, restrictedSetJudgement.getSort(set))), rewrite(pred))
      // skolem case
      case OperEx(ApalacheOper.`skolem`, OperEx(TlaBoolOper.exists, NameEx(_), set, pred))
          if restrictedSetJudgement.isRestrictedSet(set) =>
        // In the skolem case, we just treat instances of the variable name in pred as globally declared SMT
        // constants, so we don't need to introduce Exists
        rewrite(pred)
      case _ =>
        throw new RewriterException(s"QuantifierRule not applicable to $ex", ex)
    }

}
