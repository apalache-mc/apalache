package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{StrT1, ValEx}
import at.forsyte.apalache.tla.types.ModelValueHandler

/**
 * Rewrites a string literal, e.g., "hello", which is translated as a constant of the uninterpreted sort Str, or a
 * string literal of the form "foo_OF_BAR", which is translated to as a constant of the uninterpreted sort BAR.
 *
 * @author
 *   Igor Konnov
 */
class StrConstRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaStr(_)) => true
      case _                => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaStr(str)) =>
        val typeAndIndex = ModelValueHandler
          .typeAndIndex(str)
          .map(pa => (pa._1.name, pa._2))
          .getOrElse((StrT1.toString, str))
        val (newArena: Arena, newCell: ArenaCell) =
          rewriter.modelValueCache.getOrCreate(state.arena, typeAndIndex)
        state
          .setArena(newArena)
          .setRex(newCell.toBuilder)
      case _ =>
        throw new RewriterException(getClass.getSimpleName + " is not applicable", state.ex)
    }
  }
}
