package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.BoolType
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-AND[1-4].
  *
  * @author Igor Konnov
  */
class AndRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.and, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    def isTrue(e: TlaEx) = e == state.arena.cellTrue().toNameEx
    def isFalse(e: TlaEx) = e == state.arena.cellFalse().toNameEx
    state.ex match {
      case OperEx(TlaBoolOper.and, args@_*) =>
        val (newState: SymbState, newEs: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state, args)
        val noTrues = newEs.filter(r => !isTrue(r))
        if (noTrues.isEmpty) {
          // empty conjunction is always true
          newState.setRex(newState.arena.cellTrue().toNameEx)
        } else {
          if (noTrues.exists(isFalse)) {
            // one false constant makes the conjunction false
            newState.setRex(newState.arena.cellFalse().toNameEx)
          } else {
            // the boring general case
            val newArena = newState.arena.appendCell(BoolType())
            val newCell = newArena.topCell
            val cmps = noTrues.map(nameEx => OperEx(TlaOper.eq, nameEx, newArena.cellTrue().toNameEx))
            val cons = OperEx(TlaBoolOper.equiv,
              OperEx(TlaOper.eq, newCell.toNameEx, newArena.cellTrue().toNameEx),
              OperEx(TlaBoolOper.and, cmps: _*))
            newState.solverCtx.assertCellExpr(cons)
            newState.setRex(newCell.toNameEx).setArena(newArena)
          }
        }

      case _ =>
        throw new RewriterException("AndRule is not applicable")
    }
  }
}
