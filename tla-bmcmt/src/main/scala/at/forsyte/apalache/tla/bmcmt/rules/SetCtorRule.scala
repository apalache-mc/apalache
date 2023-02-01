package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.FixedElemPtr
import at.forsyte.apalache.tla.bmcmt.types.{CellT, CellTFrom}
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{OperEx, SetT1, TlaEx, TypingException}
import at.forsyte.apalache.tla.types.tla

/**
 * Rewrites the set constructor {e_1, ..., e_k}.
 *
 * @author
 *   Igor Konnov
 */
class SetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.enumSet, _*) => true
      case _                              => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaSetOper.enumSet, elems @ _*) =>
        // Rewrite the elements and remove the duplicate cells.
        // This does not guarantee us that all duplicates are removed,
        // as some cells may happen to be equal only in some models.
        val (newState, newEs: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state, elems)
        var nextState = newState
        val cells = newEs.map(nextState.arena.findCellByNameEx).toList.distinct
        val setT = CellT.fromTypeTag(ex.typeTag)
        val elemType = setT match {
          case CellTFrom(SetT1(et)) => et
          case setT @ _             => throw new TypingException("Expected a finite set, found: " + setT, state.ex.ID)
        }
        nextState = nextState.updateArena(_.appendCell(SetT1(elemType)))
        val newSetCell = nextState.arena.topCell
        nextState = nextState.updateArena(_.appendHas(newSetCell, cells.map(FixedElemPtr): _*))

        for (c <- cells) {
          val inExpr = tla.storeInSet(c.toBuilder, newSetCell.toBuilder)
          rewriter.solverContext.assertGroundExpr(inExpr)
        }

        nextState.setRex(newSetCell.toBuilder)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
