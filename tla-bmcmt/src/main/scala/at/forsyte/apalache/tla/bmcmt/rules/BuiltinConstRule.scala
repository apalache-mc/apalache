package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.predef.{TlaBoolSet, TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, ValEx}

/**
  * Rewriting BOOLEAN, Int, and Nat into predefined cells.
  *
  * @author Igor Konnov
   */
class BuiltinConstRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaFalse) | ValEx(TlaTrue) | ValEx(TlaBoolSet) | ValEx(TlaNatSet) | ValEx(TlaIntSet) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaFalse) =>
        if (state.theory == CellTheory()) {
          state.setRex(NameEx(state.arena.cellFalse().toString))
        } else {
          state.setRex(NameEx(SolverContext.falseConst))
        }

      case ValEx(TlaTrue) =>
        if (state.theory == CellTheory()) {
          state.setRex(NameEx(state.arena.cellTrue().toString))
        } else {
          state.setRex(NameEx(SolverContext.trueConst))
        }

      case ValEx(TlaBoolSet) =>
        state.setRex(NameEx(state.arena.cellBooleanSet().toString))

      case ValEx(TlaNatSet) =>
        state.setRex(NameEx(state.arena.cellNatSet().toString))

      case ValEx(TlaIntSet) =>
        state.setRex(NameEx(state.arena.cellIntSet().toString))

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
