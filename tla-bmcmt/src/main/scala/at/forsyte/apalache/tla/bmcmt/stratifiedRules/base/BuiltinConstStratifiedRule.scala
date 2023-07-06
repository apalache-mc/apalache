package at.forsyte.apalache.tla.bmcmt.stratifiedRules.base

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.StratifiedRuleInterface
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.RewriterScope
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaBoolSet, TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}

/**
 * Rewriting TRUE, FALSE, BOOLEAN, Int, and Nat into predefined cells.
 *
 * Extends [[StratifiedRuleInterface]] directly, since there's no arena/constraint manipulation.
 *
 * @author
 *   Jure Kukovec
 */
class BuiltinConstStratifiedRule extends StratifiedRuleInterface {
  def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case ValEx(TlaBool(false)) | ValEx(TlaBool(true)) | ValEx(TlaBoolSet) | ValEx(TlaNatSet) | ValEx(TlaIntSet) =>
      true
    case _ => false

  }

  def apply(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell) = {
    val arena = startingScope.arena
    val cell = ex match {
      case ValEx(TlaBool(false)) => PureArena.cellFalse(arena)
      case ValEx(TlaBool(true))  => PureArena.cellTrue(arena)
      case ValEx(TlaBoolSet)     => PureArena.cellBooleanSet(arena)
      case ValEx(TlaNatSet)      => PureArena.cellNatSet(arena)
      case ValEx(TlaIntSet)      => PureArena.cellIntSet(arena)
      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), ex)
    }
    (startingScope, cell)
  }
}
