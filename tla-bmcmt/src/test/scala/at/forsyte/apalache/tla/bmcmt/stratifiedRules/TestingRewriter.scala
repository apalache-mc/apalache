package at.forsyte.apalache.tla.bmcmt.stratifiedRules

import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.RewriterImpl
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, PureArena}
import at.forsyte.apalache.tla.lir.{TlaEx, UID}

case object NoRule extends StratifiedRuleInterface {
  override def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = false
  def apply(ex: TlaEx)(startingScope: RewriterScope): RuleOutput = (startingScope, PureArena.cellInvalid)
}

/**
 * A variant of [[RewriterImpl]], meant for testing during ongoing development.
 *
 * `cheatyMap` allows us to pre-assign cells to UIDs, such that TLA expressions, which would trigger rewriting rules
 * that aren't implemented yet, instead "rewrite" to the cells defined in the map.
 *
 * Additionally, anny assert statements are merely collected in a sequence, instead of e.g. propagating to z3.
 *
 * @author
 *   Jure Kukovec
 */
sealed case class TestingRewriter(var cheatyMap: Map[UID, ArenaCell])
    extends RewriterImpl(new Z3SolverContext(SolverConfig.default)) {
  def rewrite(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell) =
    ruleLookupTable.get(key(ex)) match {
      case Some(rule) => rule.apply(ex)(startingScope)
      case None =>
        (startingScope, cheatyMap(ex.ID))
    }

  var assertSeq: Seq[TlaEx] = Seq.empty

  override def assert(ex: TlaEx): Unit = {
    assertSeq = assertSeq :+ ex
  }

}
