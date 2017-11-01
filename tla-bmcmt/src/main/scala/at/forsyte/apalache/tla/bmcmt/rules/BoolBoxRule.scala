package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.predef.TlaBoolSet
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, ValEx}

/**
  * Implements the rules: SE-BOOL-BOX{FALSE,TRUE} and SE-SET-BOOLEAN.
  *
  * @author Igor Konnov
   */
class BoolBoxRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaFalse) => true
      case ValEx(TlaTrue) => true
      case ValEx(TlaBoolSet) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaFalse) =>
        state.setRex(NameEx(state.arena.cellFalse().toString))

      case ValEx(TlaTrue) =>
        state.setRex(NameEx(state.arena.cellTrue().toString))

      case ValEx(TlaBoolSet) =>
        state.setRex(NameEx(state.arena.cellBoolean().toString))

      case _ =>
        throw new RewriterException("LogicConstRule is not applicable")
    }
  }
}
