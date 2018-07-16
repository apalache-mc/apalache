package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

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
      case OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx)
          if state.theory == BoolTheory() =>
        // the result is expected to be Boolean => we directly work at the propositional level
        val predState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()).setRex(predEx))
        val thenState = rewriter.rewriteUntilDone(predState.setTheory(BoolTheory()).setRex(thenEx))
        val elseState = rewriter.rewriteUntilDone(thenState.setTheory(BoolTheory()).setRex(elseEx))
        val result = rewriter.solverContext.introBoolConst()
        val iffIte = tla.equiv(NameEx(result), tla.ite(predState.ex, thenState.ex, elseState.ex))
        rewriter.solverContext.assertGroundExpr(iffIte)
        coverFailurePredicates(predState, thenState, elseState)
        elseState.setRex(NameEx(result)).setTheory(BoolTheory())

      case OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        // in the general case, the both branches returns cells
        val predState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()).setRex(predEx))
        val thenState = rewriter.rewriteUntilDone(predState.setTheory(CellTheory()).setRex(thenEx))
        val elseState = rewriter.rewriteUntilDone(thenState.setTheory(CellTheory()).setRex(elseEx))
        coverFailurePredicates(predState, thenState, elseState)
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

  /**
    * This function adds the constraints that allow us to properly treat side effects such as Assert(..).
    * It essentially says that the failure predicates generated for each branch can be only activated,
    * if the branch condition is satisfied. Without this condition the expressions such as
    * "IF e \in DOMAIN f THEN f[e] ELSE default" would report a false runtime error.
    *
    * @param predState the state after rewriting the condition
    * @param thenState the state after rewriting the then branch
    * @param elseState the state after rewriting the else branch
    */
  private def coverFailurePredicates(predState: SymbState, thenState: SymbState, elseState: SymbState): Unit = {
    // XXX: future self, the operations on the maps and sets are probably expensive. Optimize.
    val predsBefore = Set(predState.arena.findCellsByType(FailPredT()) :_*)
    val thenPreds = Set(thenState.arena.findCellsByType(FailPredT()) :_*) -- predsBefore
    val elsePreds = Set(elseState.arena.findCellsByType(FailPredT()) :_*) -- thenPreds
    val cond = predState.ex
    // for each failure fp on the then branch, fp => cond
    thenPreds.foreach(fp => rewriter.solverContext.assertGroundExpr(tla.or(tla.not(fp), cond)))
    // for each failure fp on the else branch, fp => ~cond
    elsePreds.foreach(fp => rewriter.solverContext.assertGroundExpr(tla.or(tla.not(fp), tla.not(cond))))
  }

  private def iteBasic(state: SymbState, commonType: CellT, pred: TlaEx, thenCell: ArenaCell, elseCell: ArenaCell) = {
    val newArena = state.arena.appendCell(commonType)
    val newCell = newArena.topCell
    // it's OK to use the SMT equality and ite, as we are dealing with the basic types here
    val iffIte = tla.eql(newCell, tla.ite(pred, thenCell, elseCell))
    rewriter.solverContext.assertGroundExpr(iffIte)
    state.setArena(newArena).setRex(newCell.toNameEx)
  }

  // TODO: introduce this rule in the semantics report
  private def iteSet(state: SymbState, commonType: CellT, pred: TlaEx, thenCell: ArenaCell, elseCell: ArenaCell) = {
    var newArena = state.arena.appendCell(commonType)
    val newSetCell = newArena.topCell
    // make a union and introduce conditional membership
    val thenElems = Set(state.arena.getHas(thenCell) :_*)
    val elseElems = Set(state.arena.getHas(elseCell) :_*)
    newArena = (thenElems ++ elseElems).foldLeft(newArena)((a, e) => a.appendHas(newSetCell, e))
    // x \in NewSet <=> (~p \/ x \in S1) /\ (p \/ x \in S2)
    def addCellCons(elemCell: ArenaCell): Unit = {
      val inUnion = tla.in(elemCell, newSetCell)
      val inThenSet = if (thenElems.contains(elemCell)) tla.in(elemCell, thenCell) else tla.bool(false)
      val inElseSet = if (elseElems.contains(elemCell)) tla.in(elemCell, elseCell) else tla.bool(false)
      val inLeftOrRight = tla.ite(pred, inThenSet, inElseSet)
      rewriter.solverContext.assertGroundExpr(tla.eql(inUnion, inLeftOrRight))
    }

    // add SMT constraints
    for (cell <- thenElems ++ elseElems)
      addCellCons(cell)

    state.setTheory(CellTheory()).setArena(newArena).setRex(newSetCell.toNameEx)
  }
}
