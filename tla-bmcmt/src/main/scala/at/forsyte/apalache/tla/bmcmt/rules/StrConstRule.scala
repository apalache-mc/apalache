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
        ModelValueHandler.typeAndIndex(str) match {
          case Some((ConstT1(utype), index)) =>
            val (newArena: Arena, newCell: ArenaCell) =
              rewriter.modelValueCache.getOrCreate(state.arena, (utype, index))
            state
              .setArena(newArena)
              .setRex(newCell.toNameEx)
          case _ =>
            val (newArena: Arena, newCell: ArenaCell) =
              rewriter.modelValueCache.getOrCreate(state.arena, (ModelValueHandler.STRING_TYPE, str))
            state
              .setArena(newArena)
              .setRex(newCell.toNameEx)
        }

      case _ =>
        throw new RewriterException(getClass.getSimpleName + " is not applicable", state.ex)
    }
  }
}
