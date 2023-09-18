package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * FormulaRule is analogous to RewritingRule, except that it produces a Term translation directly, while possibly
 * discharging declarations. It is side-effect free, instead of mutating the arena and solver context.
 *
 * @author
 *   Jure Kukovec
 */
trait FormulaRule {
  def isApplicable(ex: TlaEx): Boolean

  def apply(ex: TlaEx): TermBuilderT
}
