package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.formulas.{Sort, Term}

trait FormulaRule {
  def isApplicable(ex: TlaEx): Boolean

  def apply(ex: TlaEx): Term
}
