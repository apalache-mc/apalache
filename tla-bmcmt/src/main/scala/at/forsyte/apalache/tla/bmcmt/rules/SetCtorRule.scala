package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{CellT, FinSetT}
import at.forsyte.apalache.tla.bmcmt.util.ConsChainUtil
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{BuilderEx, OperEx, TlaEx, TlaType1, TypingException}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla

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
        val (newState, newEs: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state, elems)
        var nextState = newState
        val cells = newEs.map(nextState.arena.findCellByNameEx)
        val setT = CellT.fromTypeTag(ex.typeTag)
        val elemType = setT match {
          case FinSetT(et) => et
          case setT @ _    => throw new TypingException("Expected a finite set, found: " + setT, state.ex.ID)
        }
        nextState = nextState.updateArena(_.appendCell(FinSetT(elemType)))
        val newSetCell = nextState.arena.topCell
        nextState = nextState.updateArena(_.appendHas(newSetCell, cells: _*))

        if (cells.nonEmpty) {
          def consChain(elems: Seq[ArenaCell]): BuilderEx =
            ConsChainUtil.consChainFold[ArenaCell](
                elems,
                newSetCell.toNameEx,
                { cell =>
                  val inSet = tla.apalacheStoreInSet(cell.toNameEx, newSetCell.toNameEx)
                  (inSet, tla.bool(true))
                },
            )

          val cons = consChain(cells)
          rewriter.solverContext.assertGroundExpr(tla.apalacheAssignChain(newSetCell.toNameEx, cons))
        }

        nextState.setRex(newSetCell.toNameEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
