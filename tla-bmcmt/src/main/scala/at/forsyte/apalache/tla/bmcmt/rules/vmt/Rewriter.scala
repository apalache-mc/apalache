package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.formulas.{Sort, Term}

abstract class Rewriter[T <: Sort] {
  def rewrite(ex: TlaEx): Term[T]
}
