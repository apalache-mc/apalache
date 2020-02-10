package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, NullEx, OperEx, TlaEx}

/**
  * Rewrites a set comprehension { x \in S: P }.
  *
  * @author Igor Konnov
  */
class SetFilterRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.filter, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.filter, NameEx(varName), setEx, predEx) =>
        // rewrite the set expression into a memory cell
        var newState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(setEx))
        newState = newState.asCell.cellType match {
          case FinSetT(_) => newState
          case tp @ _ => throw new NotImplementedError("A set filter over %s is not implemented".format(tp))
        }
        val setCell = newState.asCell

        // unfold the set and produce boolean constants for every potential element
        val potentialCells = newState.arena.getHas(setCell)
        // similar to SymbStateRewriter.rewriteSeqUntilDone, but also handling exceptions

        def eachElem(potentialCell: ArenaCell): TlaEx = {
          // add [cell/x]
          val newBinding = newState.binding + (varName -> potentialCell)
          val cellState = new SymbState(predEx, BoolTheory(), newState.arena, newBinding)
          val ns = rewriter.rewriteUntilDone(cellState)
          newState = ns.setBinding(ns.binding - varName) // reset binding
          ns.ex
        }

        // compute predicates for all the cells, some may statically result in NullEx
        val computedPreds: Seq[TlaEx] = potentialCells map eachElem
        val filteredCellsAndPreds = (potentialCells zip computedPreds) filter (_._2 != NullEx)

        // get the result type from the type finder
        val resultType = rewriter.typeFinder.compute(state.ex, ConstT(), setCell.cellType, BoolT())
        assert(PartialFunction.cond(resultType) { case FinSetT(_) => true })

        // introduce a new set
        val arena = newState.arena.appendCell(resultType)
        val newSetCell = arena.topCell
        val newArena = arena.appendHas(newSetCell, filteredCellsAndPreds.map(_._1): _*)

        // require each cell to satisfy the predicate
        def addCellCons(cell: ArenaCell, pred: TlaEx): Unit = {
          val inNewSet = OperEx(TlaSetOper.in, cell.toNameEx, newSetCell.toNameEx)
          val inOldSet = OperEx(TlaSetOper.in, cell.toNameEx, setCell.toNameEx)
          val inOldSetAndPred = OperEx(TlaBoolOper.and, pred, inOldSet)
          val ifAndOnlyIf = OperEx(TlaOper.eq, inNewSet, inOldSetAndPred)
          rewriter.solverContext.assertGroundExpr(ifAndOnlyIf)
        }

        // add SMT constraints
        for ((cell, pred) <- filteredCellsAndPreds)
          addCellCons(cell, pred)

        val finalState =
          newState.setTheory(CellTheory())
            .setArena(newArena).setRex(newSetCell.toNameEx)
        rewriter.coerce(finalState, state.theory) // coerce to the source theory

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
