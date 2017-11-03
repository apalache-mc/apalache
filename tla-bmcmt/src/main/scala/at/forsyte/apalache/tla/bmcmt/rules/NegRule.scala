package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.BoolType
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * Implements the rules: SE-BOOL-NEG[1-9].
  *
  * @author Igor Konnov
  */
class NegRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.not, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaBoolOper.not, ex @NameEx(name)) =>
        // SE-BOOL-NEG9
        if (name == state.arena.cellFalse().toString) {
          state.setRex(state.arena.cellTrue().toNameEx)
        } else if (name == state.arena.cellTrue().toString) {
          state.setRex(state.arena.cellFalse().toNameEx)
        } else {
          val newArena = state.arena.appendCell(BoolType())
          val newCell = newArena.topCell
          state.solverCtx.assertCellExpr(OperEx(TlaOper.ne, ex, newCell.toNameEx))
          state.setArena(newArena).setRex(newCell.toNameEx)
        }

      case OperEx(TlaBoolOper.not, ex: TlaEx) =>
        // SE-BOOL-NEG[1-8]
        state.setRex(rewriteNot(ex))

      case _ =>
        throw new RewriterException("NegRule is not applicable")
    }
  }

  private def rewriteNot(root: TlaEx) = {
    root match {
      case OperEx(TlaBoolOper.or, es@_*) =>             // SE-BOOL-NEG1
        OperEx(TlaBoolOper.and, es.map(e => OperEx(TlaBoolOper.not, e)): _*)

      case OperEx(TlaBoolOper.and, es@_*) =>            // SE-BOOL-NEG2
        OperEx(TlaBoolOper.or, es.map(e => OperEx(TlaBoolOper.not, e)): _*)

      case OperEx(TlaBoolOper.implies, lhs, rhs) =>     // SE-BOOL-NEG3
        OperEx(TlaBoolOper.and,
          lhs, OperEx(TlaBoolOper.not, rhs))

      case OperEx(TlaBoolOper.equiv, lhs, rhs) =>       // SE-BOOL-NEG4
        OperEx(TlaBoolOper.equiv,
          OperEx(TlaBoolOper.not, lhs),
          rhs)

      case OperEx(TlaBoolOper.not, e) => e              // SE-BOOL-NEG5

      case OperEx(TlaBoolOper.exists, x, set, pred) =>  // SE-BOOL-NEG6
        OperEx(TlaBoolOper.forall,
          x, set,
          OperEx(TlaBoolOper.not, pred))

      case OperEx(TlaBoolOper.forall, x, set, pred) =>  // SE-BOOL-NEG7
        OperEx(TlaBoolOper.exists,
          x, set,
          OperEx(TlaBoolOper.not, pred))

      case _ =>
        throw new RewriterException("NegRule is not applicable")
    }
  }
}
