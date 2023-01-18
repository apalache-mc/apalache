package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.ElemPtr
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, NullEx, OperEx, SetT1, TlaEx, TlaType1}

/**
 * Rewrites a set comprehension { x \in S: P }.
 *
 * @author
 *   Igor Konnov
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
          case CellTFrom(SetT1(_)) => newState
          case tp @ _ => throw new NotImplementedError("A set filter over %s is not implemented".format(tp))
        }
        val setCell = newState.asCell

        // unfold the set and produce boolean constants for every potential element
        val potentialCells = newState.arena.getHasPtr(setCell)
        // similar to SymbStateRewriter.rewriteSeqUntilDone, but also handling exceptions

        def eachElem(potentialCell: ElemPtr): TlaEx = {
          // add [cell/x]
          val newBinding = Binding(newState.binding.toMap + (varName -> potentialCell.elem))
          val cellState = new SymbState(predEx, newState.arena, newBinding)
          val ns = rewriter.rewriteUntilDone(cellState)
          newState = ns.setBinding(Binding(ns.binding.toMap - varName)) // reset binding
          ns.ex
        }

        // compute predicates for all the cells, some may statically result in NullEx
        val computedPreds: Seq[TlaEx] = potentialCells.map(eachElem)
        val filteredCellsAndPreds = (potentialCells.zip(computedPreds)).filter(_._2 != NullEx)

        // get the result type from the type finder
        val resultType = TlaType1.fromTypeTag(ex.typeTag)
        assert(resultType.isInstanceOf[SetT1])

        // introduce a new set
        val arena = newState.arena.appendCell(resultType)
        val newSetCell = arena.topCell
        val newArena = arena.appendHas(newSetCell, filteredCellsAndPreds.map(_._1): _*)

        // require each cell to satisfy the predicate
        def addCellCons(cellPtr: ElemPtr, pred: TlaEx): Unit = {
          val cell = cellPtr.elem
          val inNewSet = tla.storeInSet(cell.toBuilder, newSetCell.toBuilder)
          val notInNewSet = tla.storeNotInSet(cell.toBuilder, newSetCell.toBuilder) // cell is not in newSetCell
          val inOldSet = tla.selectInSet(cell.toBuilder, setCell.toBuilder)
          val inOldSetAndPred = tla.and(tla.unchecked(pred), inOldSet)
          val ite = tla.ite(inOldSetAndPred, inNewSet, notInNewSet)
          rewriter.solverContext.assertGroundExpr(ite)
        }

        // variant of addCellCons for use with SMT maps, which unconstrained newSetCell
        def addCellConsForUnconstrainedNewSetCell(cellPtr: ElemPtr, pred: TlaEx): Unit = {
          val cell = cellPtr.elem
          // since newSetCell is assumed to be unconstrained we simple use SMT select here
          val inNewSet = tla.selectInSet(cell.toBuilder, newSetCell.toBuilder)
          val notInNewSet = tla.not(tla.selectInSet(cell.toBuilder, newSetCell.toBuilder))
          val ite = tla.ite(tla.unchecked(pred), inNewSet, notInNewSet)
          rewriter.solverContext.assertGroundExpr(ite)
        }

        // add SMT constraints
        rewriter.solverContext.config.smtEncoding match {
          case SMTEncoding.Arrays =>
            // we make an unconstrained array, constrain its needed entries, and intersect it with setCell using smtMap
            rewriter.solverContext.assertGroundExpr(tla.unconstrainArray(newSetCell.toBuilder))
            for ((cell, pred) <- filteredCellsAndPreds)
              addCellConsForUnconstrainedNewSetCell(cell, pred)
            // using SMT map with conjunction ensures that elements of newSetCell are added only if they are present in
            // setCell, so we don't need membership constraints in addCellConsForUnconstrainedNewSetCell
            val smtMap = tla.smtMap(TlaBoolOper.and, setCell.toBuilder, newSetCell.toBuilder)
            rewriter.solverContext.assertGroundExpr(smtMap)

          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            for ((cell, pred) <- filteredCellsAndPreds)
              addCellCons(cell, pred)

          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

        newState.setArena(newArena).setRex(newSetCell.toBuilder)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
