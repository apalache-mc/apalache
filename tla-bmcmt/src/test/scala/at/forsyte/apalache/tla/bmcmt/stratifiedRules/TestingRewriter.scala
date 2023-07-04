package at.forsyte.apalache.tla.bmcmt.stratifiedRules

import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.{RewriterImpl, RewriterScope}
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, PureArena}
import at.forsyte.apalache.tla.lir.{TlaEx, TlaType1, UID}

case object NoRule extends StratifiedRuleInterface {
  override def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = false
  def apply(ex: TlaEx)(startingScope: RewriterScope): RuleOutput = (startingScope, PureArena.cellInvalid)
}

/**
 * Since not all rules are implemented yet, we can cheat a bit with an auxiliary ID -> cell map.
 *
 * @author
 *   Jure Kukovec
 */
sealed case class TestingRewriter(var cheatyMap: Map[UID, ArenaCell])
    extends RewriterImpl(new Z3SolverContext(SolverConfig.default)) {
  def rewrite(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell) = {
    ruleLookupTable.get(key(ex)) match {
      case Some(rule) => rule.apply(ex)(startingScope)
      case None =>
        (startingScope, cheatyMap(ex.ID))
    }
  }

  var assertSeq: Seq[TlaEx] = Seq.empty

  override def assert(ex: TlaEx): Unit = {
    assertSeq = assertSeq :+ ex
  }

  def load(initArena: PureArena)(vars: (UID, TlaType1)*): PureArena =
    vars.foldLeft(initArena) { case (arena, (id, exprType)) =>
      val (retArena, exprCell) = addCell(arena, exprType)
      cheatyMap += id -> exprCell
      retArena
    }

}
