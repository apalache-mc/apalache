package at.forsyte.apalache.tla.bmcmt.rules.vmt
import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

/**
 * The ToTermRewriter implementation from reTLA to SMT Terms.
 *
 * @author
 *   Jure Kukovec
 */
class ToTermRewriterImpl(constSets: ConstSetMapT, gen: UniqueNameGenerator) extends ToTermRewriter {
  // Less optimized rule lookup than SymbStateRewriter, since we have fewer rules, just search the list
  private val setJudgement = new RestrictedSetJudgement(constSets)
  private val rules: List[FormulaRule] = List(
      new BoolRule(this),
      new QuantifierRule(this, setJudgement),
      new EUFRule(this, setJudgement, gen),
      new ValueRule,
  )

  override def rewrite(ex: TlaEx): TermBuilderT =
    rules.find(r => r.isApplicable(ex)) match {
      case Some(r) =>
        r(ex)

      case None =>
        throw new RewriterException(s"No rule applies to $ex", ex)
    }
}

object ToTermRewriterImpl {
  def apply(
      constSets: ConstSetMapT = Map.empty,
      generator: UniqueNameGenerator = new UniqueNameGenerator): ToTermRewriter =
    new ToTermRewriterImpl(constSets, generator)
}
