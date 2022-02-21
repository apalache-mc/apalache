package at.forsyte.apalache.tla.bmcmt.rules.vmt
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.{Continue, NoRule}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.formulas.{Sort, Term}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

class RewriterImpl(constSets: ConstSetMapT, gen: UniqueNameGenerator) extends Rewriter {
  // Less optimized rule lookup than SymbStateRewriter, since we have fewer rules, just search the list
  private val setJudgement = new RestrictedSetJudgement(constSets)
  private val rules: List[FormulaRule] = List(
      new BoolRule(this),
      new QuantifierRule(this, setJudgement),
      new EUFRule(this, setJudgement, gen),
      new ValueRule,
  )

  override def rewrite(ex: TlaEx): Term =
    rules.find(r => r.isApplicable(ex)) match {
      case Some(r) =>
        r(ex)

      case None =>
        throw new RewriterException(s"No rule applies to $ex", ex)
    }
}

object RewriterImpl {
  def apply(constSets: ConstSetMapT = Map.empty, generator: UniqueNameGenerator = new UniqueNameGenerator): Rewriter =
    new RewriterImpl(constSets, generator)
}
