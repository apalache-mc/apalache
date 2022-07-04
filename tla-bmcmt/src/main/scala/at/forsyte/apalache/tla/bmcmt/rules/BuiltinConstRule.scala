package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.UntypedPredefs.untyped
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaBoolSet, TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.{NameEx, ValEx}

/**
 * Rewriting BOOLEAN, Int, and Nat into predefined cells.
 *
 * @author
 *   Igor Konnov
 */
class BuiltinConstRule extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaBool(false)) | ValEx(TlaBool(true)) | ValEx(TlaBoolSet) | ValEx(TlaNatSet) | ValEx(TlaIntSet) =>
        true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaBool(false)) =>
        state.setRex(state.arena.cellFalse().toBuilder)

      case ValEx(TlaBool(true)) =>
        state.setRex(state.arena.cellTrue().toBuilder)

      case ValEx(TlaBoolSet) =>
        state.setRex(state.arena.cellBooleanSet().toBuilder)

      case ValEx(TlaNatSet) =>
        state.setRex(NameEx(state.arena.cellNatSet().toString)(untyped))

      case ValEx(TlaIntSet) =>
        state.setRex(NameEx(state.arena.cellIntSet().toString)(untyped))

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
