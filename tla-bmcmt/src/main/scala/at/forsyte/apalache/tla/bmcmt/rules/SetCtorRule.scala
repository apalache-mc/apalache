package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.FinSetT
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-SET-CTOR[1-2].
  *
  * @author Igor Konnov
   */
class SetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.enumSet, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.enumSet, elems @ _*) =>
        // switch to cell theory
        val (newState: SymbState, newEs: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), elems)
        val cells = newEs.map(newState.arena.findCellByNameEx)
        // compute the set type using the type finder
        val elemType = rewriter.typeFinder.compute(state.ex, cells.map(_.cellType) :_*) match {
          case FinSetT(et) => et
          case setT @ _ => throw new TypeException("Expected a finite set, found: " + setT)
        }
        val arena = newState.arena.appendCell(FinSetT(elemType))
        val newCell = arena.topCell
        val newArena = arena.appendHas(newCell, cells: _*)
        def addIn(c: ArenaCell): Unit = {
          val inExpr = OperEx(TlaSetOper.in, c.toNameEx, newCell.toNameEx)
          rewriter.solverContext.assertGroundExpr(inExpr)
        }
        cells.foreach(addIn)
        val finalState =
          state.setArena(newArena).setRex(newCell.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
