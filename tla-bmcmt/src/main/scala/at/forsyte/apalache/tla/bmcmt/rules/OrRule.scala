package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.BoolType
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-OR[1-4].
  *
  * Note that this rule does not implement case split as prescribed by rule SE-SEARCH-SPLIT.
  *
  * @author Igor Konnov
  */
class OrRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.or, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    def isTrue(e: TlaEx) = e == state.arena.cellTrue().toNameEx
    def isFalse(e: TlaEx) = e == state.arena.cellFalse().toNameEx

    state.ex match {
      case OperEx(TlaBoolOper.or, args@_*) =>
        val (newState: SymbState, newRexes: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state, args)

        val noFalses = newRexes.filter(r => !isFalse(r))
        if (noFalses.isEmpty) {
          // empty disjunction is always false
          newState.setRex(newState.arena.cellFalse().toNameEx)
        } else {
          if (noFalses.exists(isTrue)) {
            // one true constant makes the disjunction true
            newState.setRex(newState.arena.cellTrue().toNameEx)
          } else {
            // the boring general case
            val newArena = newState.arena.appendCell(BoolType())
            val newCell = newArena.topCell
            val cmps = noFalses.map(nameEx => OperEx(TlaOper.eq, nameEx, newArena.cellTrue().toNameEx))
            val cons = OperEx(TlaBoolOper.equiv,
              OperEx(TlaOper.eq, newCell.toNameEx, newArena.cellTrue().toNameEx),
              OperEx(TlaBoolOper.or, cmps: _*))
            newState.solverCtx.assertCellExpr(cons)
            newState.setRex(newCell.toNameEx).setArena(newArena)
          }
        }

      case _ =>
        throw new RewriterException("OrRule is not applicable")
    }
  }
}
