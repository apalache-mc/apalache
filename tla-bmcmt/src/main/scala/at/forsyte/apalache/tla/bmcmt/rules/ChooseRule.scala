package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper


/**
  * Implements the rules: SE-LOG-CHO1.
  * Similar to TLC, we implement a non-deterministic choice.
  * It is not hard to add the requirement of determinism, but that will
  * probably affect efficiency.
  *
  * TODO: add determinism as an option.
  *
  * @author Igor Konnov
  */
class ChooseRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickRule = new CherryPick(rewriter)

  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(TlaOper.chooseBounded, _, _, _) =>
        true

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaOper.chooseBounded, varName, set, pred) =>
        def solverAssert = rewriter.solverContext.assertGroundExpr _
        // compute set comprehension and then pick an element from it
        val filterEx = tla.filter(varName, set, pred)
        var nextState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(filterEx))
        // pick an arbitrary witness
        val setCell = nextState.arena.findCellByNameEx(nextState.ex)
        if (nextState.arena.getHas(setCell).nonEmpty) {
          val elems = nextState.arena.getHas(setCell)
          val nelems = elems.size
          // add an oracle \in 0..N, where the indices from 0 to N - 1 correspond to the set elements,
          // whereas the index N corresponds to the default choice when the set is empty
          nextState = nextState.setArena(nextState.arena.appendCell(IntT()))
          val oracle = nextState.arena.topCell.toNameEx
          solverAssert(tla.ge(oracle, tla.int(0)))
          solverAssert(tla.le(oracle, tla.int(nelems)))
          // introduce a default value
          nextState = makeUpValue(nextState, findElemType(setCell))
          val defaultValue = nextState.asCell
          // when oracle = N, the set must be empty
          val setIsEmpty = tla.and(elems.map(e => tla.notin(e.toNameEx, setCell.toNameEx)) :_*)
          solverAssert(tla.impl(tla.eql(oracle, tla.int(nelems)), setIsEmpty))
          // pick a cell
          nextState = pickRule.pickBlindly(nextState, oracle, elems)
          val pickedCell = nextState.asCell
          // require that the picked cell is in the set
          def chosenWhenIn(elem: ArenaCell, no: Int): Unit =
            solverAssert(tla.impl(tla.eql(oracle, tla.int(no)), tla.in(elem.toNameEx, setCell.toNameEx)))

          elems.zipWithIndex foreach (chosenWhenIn _).tupled
          // and when it is empty, require the result to be equal to the default value
          nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((pickedCell, defaultValue)))
          solverAssert(tla.impl(tla.eql(oracle, tla.int(nelems)), tla.eql(pickedCell.toNameEx, defaultValue.toNameEx)))
          rewriter.coerce(nextState, state.theory)
        } else {
          rewriter.coerce(makeUpValue(nextState, findElemType(setCell)), state.theory)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def findElemType(setCell: ArenaCell): CellT = {
    setCell.cellType match {
      case FinSetT(et) =>
        et

      case tp @ _ =>
        throw new RewriterException(s"Expected a set, found: $tp")
    }
  }

  // Produce a 'default' value for a given type, when CHOOSE is called against a statically empty set
  // TODO: introduce a cache for default values, otherwise there will be many identical copies
  private def makeUpValue(state: SymbState, cellType: CellT): SymbState = {
    cellType match {
      case recT @ RecordT(_) =>
        var arena = state.arena.appendCell(recT)
        val recCell = arena.topCell
        var newState = state.setArena(arena)
        for (v <- recT.fields.values) {
          newState = makeUpValue(newState, v)
          val fieldCell = newState.arena.findCellByNameEx(newState.ex)
          arena = arena.appendHas(recCell, fieldCell)
          newState = newState.setArena(arena)
        }
        // create the domain and attach it to the record
        val (newArena, domain) = rewriter.recordDomainCache.getOrCreate(newState.arena, recT.fields.keySet)
        arena = newArena
        arena = arena.setDom(recCell, domain)
        newState.setArena(arena).setRex(recCell.toNameEx)

      case IntT() =>
        rewriter.rewriteUntilDone(state.setRex(tla.int(0)))

      case BoolT() =>
        rewriter.rewriteUntilDone(state.setRex(tla.bool(false)))

      case ConstT() =>
        rewriter.rewriteUntilDone(state.setRex(tla.str("None")))

      case tp @ FinSetT(_) => // {}
        var arena = state.arena.appendCell(tp)
        val recCell = arena.topCell
        state.setRex(recCell.toNameEx).setArena(arena)

      case tp @ FunT(domT, cdmT) => // [x \in {} |-> {}]
        val domState = makeUpValue(state, domT)
        val cdmState = makeUpValue(domState, cdmT)
        var arena = state.arena.appendCell(tp)
        val funCell = arena.topCell
        arena = arena.setDom(funCell, arena.findCellByNameEx(domState.ex))
        arena = arena.setCdm(funCell, arena.findCellByNameEx(cdmState.ex))
        state.setArena(arena).setRex(funCell.toNameEx)

      case tp @ _ =>
        throw new RewriterException("Default values are not implemented for $tp")
    }
  }
}
