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
        // compute set comprehension and then pick an element from it
        val filterEx = tla.filter(varName, set, pred)
        val filterState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(filterEx))
        // pick an arbitrary witness
        val setCell = filterState.arena.findCellByNameEx(filterState.ex)
        if (filterState.arena.getHas(setCell).nonEmpty) {
          rewriter.coerce(pickRule.pick(setCell, filterState), state.theory)
        } else {
          setCell.cellType match {
            case FinSetT(et) =>
              rewriter.coerce(makeUpValue(filterState, et), state.theory)

            case tp @ _ =>
              throw new RewriterException(s"Expected a set, found: $tp")
          }
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  // produce a 'default' value for a given type, when CHOOSE is called against a statically empty set
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
