package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.util.ConsChainUtil
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{BuilderEx, NameEx, NullEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Rewrites a set comprehension { x \in S: P }.
 *
 * @author Igor Konnov
 */
class SetFilterRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.filter, _*) => true
      case _                             => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaSetOper.filter, NameEx(varName), setEx, predEx) =>
        // rewrite the set expression into a memory cell
        var newState = rewriter.rewriteUntilDone(state.setRex(setEx))
        newState = newState.asCell.cellType match {
          case FinSetT(_) => newState
          case tp @ _     => throw new NotImplementedError("A set filter over %s is not implemented".format(tp))
        }
        val setCell = newState.asCell

        // unfold the set and produce boolean constants for every potential element
        val potentialCells = newState.arena.getHas(setCell)
        // similar to SymbStateRewriter.rewriteSeqUntilDone, but also handling exceptions

        def eachElem(potentialCell: ArenaCell): TlaEx = {
          // add [cell/x]
          val newBinding = Binding(newState.binding.toMap + (varName -> potentialCell))
          val cellState = new SymbState(predEx, newState.arena, newBinding)
          val ns = rewriter.rewriteUntilDone(cellState)
          newState = ns.setBinding(Binding(ns.binding.toMap - varName)) // reset binding
          ns.ex
        }

        // compute predicates for all the cells, some may statically result in NullEx
        val computedPreds: Seq[TlaEx] = potentialCells map eachElem
        val filteredCellsAndPreds = (potentialCells zip computedPreds) filter (_._2 != NullEx)

        // get the result type from the type finder
        val resultType = CellT.fromTypeTag(ex.typeTag)
        assert(resultType.isInstanceOf[FinSetT])

        // introduce a new set
        val arena = newState.arena.appendCell(resultType)
        val newSetCell = arena.topCell
        val newArena = arena.appendHas(newSetCell, filteredCellsAndPreds.map(_._1): _*)

        // require each cell to satisfy the predicate
        def addCellCons(cellsAndPreds: Seq[(ArenaCell, TlaEx)]): Unit = {
          if (cellsAndPreds.nonEmpty) {
            def consChain(elems: Seq[(ArenaCell, TlaEx)]): BuilderEx =
              ConsChainUtil.consChainFold[(ArenaCell, TlaEx)](
                elems,
                newSetCell.toNameEx,
                { case (cell, pred) =>
                  val inNewSet = tla.apalacheStoreInSet(cell.toNameEx, newSetCell.toNameEx)
                  val inOldSet = tla.apalacheSelectInSet(cell.toNameEx, setCell.toNameEx)
                  val inOldSetAndPred = tla.and(pred, inOldSet)
                  (inNewSet, inOldSetAndPred)
                }
              )

            val cons = consChain(cellsAndPreds) // Produces a chain of SMT store
            rewriter.solverContext.assertGroundExpr(tla.apalacheAssignChain(newSetCell.toNameEx, cons))
          }
        }

        def addCellConsWithSmtMap(cellsAndPreds: Seq[(ArenaCell, TlaEx)]): Unit = {
          if (cellsAndPreds.nonEmpty) {
            def consChain(elems: Seq[(ArenaCell, TlaEx)]): BuilderEx =
              ConsChainUtil.consChainFold[(ArenaCell, TlaEx)](
                elems,
                tla.bool(true),
                { case (cell, pred) =>
                  val inNewSet = tla.apalacheSelectInSet(cell.toNameEx, newSetCell.toNameEx)
                  val inOldSet = tla.apalacheSelectInSet(cell.toNameEx, setCell.toNameEx)
                  val inOldSetAndPred = tla.and(pred, inOldSet)
                  val and = tla.and(tla.eql(inNewSet, inOldSetAndPred))
                  (and, tla.bool(true))
                }
              )

            val cons = consChain(cellsAndPreds) // Produces a chain of conjunctions of conditional SMT select
            rewriter.solverContext.assertGroundExpr(tla.apalacheSmtMap(setCell.toNameEx, cons, newSetCell.toNameEx))
          }
        }

        // add SMT constraints
        rewriter.solverContext.config.smtEncoding match {
          case `arraysEncoding` =>
            addCellConsWithSmtMap(filteredCellsAndPreds)

          case `oopsla19Encoding` =>
            addCellCons(filteredCellsAndPreds)

          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

        newState.setArena(newArena).setRex(newSetCell.toNameEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
