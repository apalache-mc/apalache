package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.{ConstT1, StrT1, ValEx}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecheck.ModelValueHandler

/**
 * Rewrites a string literal, e.g., "hello".
 *
 * @author Igor Konnov
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
          .getOrElse((ModelValueHandler.STRING_TYPE, str))
        val (newArena: Arena, newCell: ArenaCell) =
          rewriter.modelValueCache.getOrCreate(state.arena, typeAndIndex)
        state
          .setArena(newArena)
          .setRex(newCell.toNameEx)
      case _ =>
        throw new RewriterException(getClass.getSimpleName + " is not applicable", state.ex)
    }
  }
}
