package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.predef.TlaBoolSet
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, ValEx}

/**
  * Implements the rules: SE-BOOL-{FALSE,TRUE} and SE-SET-BOOLEAN.
  *
  * @author Igor Konnov
   */
class BoolConstRule(rewriter: SymbStateRewriter) extends RewritingRule {
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
        if (state.theory == CellTheory()) {
          state.setRex(NameEx(state.arena.cellFalse().toString))
        } else {
          state.setRex(NameEx(state.solverCtx.falseConst))
        }

      case ValEx(TlaTrue) =>
        if (state.theory == CellTheory()) {
          state.setRex(NameEx(state.arena.cellTrue().toString))
        } else {
          state.setRex(NameEx(state.solverCtx.trueConst))
        }

      case ValEx(TlaBoolSet) =>
        state.setRex(NameEx(state.arena.cellBoolean().toString))

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
