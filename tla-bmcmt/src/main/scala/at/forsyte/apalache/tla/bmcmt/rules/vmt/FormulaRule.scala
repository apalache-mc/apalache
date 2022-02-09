package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.formulas.{Sort, Term}

trait FormulaRule[T <: Sort] {
  def isApplicable(ex: TlaEx): Boolean

  def apply(ex: TlaEx): Term[T]
}
