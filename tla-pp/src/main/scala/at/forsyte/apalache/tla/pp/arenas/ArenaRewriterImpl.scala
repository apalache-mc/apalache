package at.forsyte.apalache.tla.pp.arenas

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.pp.arenas.rules.{AssignmentArenaRule, SetCupArenaRule, SubstArenaRule}

import scalaz._
import scalaz.Scalaz._

/**
 * @author
 *   Jure Kukovec
 */
class ArenaRewriterImpl extends ArenaRewriter {
  // TODO: Eventually use same map as current BMC, this is just placeholder. Linear-search is slow.
  private val rules: IndexedSeq[ArenaRule] = IndexedSeq(
      new SubstArenaRule,
      new AssignmentArenaRule(this),
      new SetCupArenaRule(this),
  )

  private def findApplicable(ex: TlaEx): ArenaComputationInternalState[Option[ArenaRule]] =
    rules.foldLeft(Option.empty[ArenaRule].point[ArenaComputationInternalState]) { case (optCmp, rule) =>
      for {
        opt <- optCmp
        applicable <- rule.isApplicable(ex)
      } yield
        if (opt.nonEmpty) opt
        else if (applicable) Some(rule)
        else None
    }

  override def rewrite(tlaEx: TlaEx): ArenaComputation = for {
    ruleOpt <- findApplicable(tlaEx)
  } yield ruleOpt match {
    case Some(rule) => rule.apply(tlaEx)
    case None       => throw new Exception("Not supported.")
  }
}
