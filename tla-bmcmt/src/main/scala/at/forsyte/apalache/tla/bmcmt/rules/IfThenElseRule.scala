package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-ITE[1-6].
  *
  * @author Igor Konnov
  */
class IfThenElseRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaControlOper.ifThenElse, _, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        val predState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()).setRex(predEx))
        val thenState = rewriter.rewriteUntilDone(predState.setTheory(CellTheory()).setRex(thenEx))
        val elseState = rewriter.rewriteUntilDone(thenState.setTheory(CellTheory()).setRex(elseEx))
        val thenCell = elseState.arena.findCellByNameEx(thenState.ex)
        val elseCell = elseState.arena.findCellByNameEx(elseState.ex)
        val commonType = thenCell.cellType.unify(elseCell.cellType)
        if (commonType.isEmpty) {
          throw new RewriterException("Failed to unify %s and %s in IF-THEN-ELSE"
            .format(thenCell.cellType, elseCell.cellType))
        }
        val pred = predState.ex
        (thenCell.cellType, elseCell.cellType) match {
          // ITE[1-4]
          case (BoolT(), BoolT()) | (IntT(), IntT()) | (ConstT(), ConstT()) =>
            val finalState = iteBasic(elseState, commonType.get, pred, thenCell, elseCell)
            rewriter.coerce(finalState, state.theory) // coerce to the source theory

          // ITE5
          case (FinSetT(_), FinSetT(_)) =>
            val finalState = iteSet(elseState, commonType.get, pred, thenCell, elseCell)
            rewriter.coerce(finalState, state.theory) // coerce to the source theory

          // TODO: the general case ITE6 is missing
          case _ =>
            throw new RewriterException("Attempting to apply IF-THEN-ELSE to %s and %s, not supported"
              .format(thenCell.cellType, elseCell.cellType))
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def iteBasic(state: SymbState, commonType: CellT, pred: TlaEx, thenCell: ArenaCell, elseCell: ArenaCell) = {
    val newArena = state.arena.appendCell(commonType)
    val newCell = newArena.topCell
    // it's OK to use the SMT equality, as we are dealing with the basic types here
    val ifCond = tla.and(pred, tla.eql(newCell, thenCell))
    val elseCond = tla.and(tla.not(pred), tla.eql(newCell, elseCell))
    rewriter.solverContext.assertGroundExpr(tla.or(ifCond, elseCond))
    state.setArena(newArena).setRex(newCell.toNameEx)
  }

  // TODO: introduce this rule in the semantics report
  private def iteSet(state: SymbState, commonType: CellT, pred: TlaEx, thenCell: ArenaCell, elseCell: ArenaCell) = {
    val newArena = state.arena.appendCell(commonType)
    val newSetCell = newArena.topCell
    // make a union and introduce conditional membership
    val ifElems = state.arena.getHas(thenCell)
    val thenElems = state.arena.getHas(elseCell)
    val newArena2 = (ifElems ++ thenElems).foldLeft(newArena)((a, e) => a.appendHas(newSetCell, e))
    // x \in NewSet <=> (~p \/ x \in S1) /\ (p \/ x \in S2)
    def addCellCons(elemCell: ArenaCell): Unit = {
      val inUnion = tla.in(elemCell, newSetCell)
      val inLeftSet = tla.in(elemCell, thenCell)
      val inRightSet = tla.in(elemCell, elseCell)
      val inLeftOrRight = tla.and(tla.or(tla.not(pred), inLeftSet), tla.or(pred, inRightSet))
      rewriter.solverContext.assertGroundExpr(tla.eql(inUnion, inLeftOrRight))
    }

    // add SMT constraints
    for (cell <- ifElems ++ thenElems)
      addCellCons(cell)

    state.setTheory(CellTheory()).setArena(newArena2).setRex(newSetCell.toNameEx)
  }
}
