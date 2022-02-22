package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.formulas.Term

abstract class Rewriter {
  def rewrite(ex: TlaEx): Term
}
