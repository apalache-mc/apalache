package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.formulas.Term

/**
 * FormulaRule is analogous to RewritingRule, except that it produces a Term translation directly. It is side-effect
 * free, instead of mutating the arena and solver context.
 *
 * @author
 *   Jure Kukovec
 */
trait FormulaRule {
  def isApplicable(ex: TlaEx): Boolean

  def apply(ex: TlaEx): Term
}
