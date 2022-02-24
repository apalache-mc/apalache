package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.formulas.Term

/**
 * Rewriter defines a translation from TLA+ to SMT Terms.
 *
 * @author
 *   Jure Kukovec
 */
abstract class Rewriter {
  def rewrite(ex: TlaEx): Term
}
