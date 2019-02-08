package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla

/**
  * Given a type, this class produces a default value for that type. This is needed by ChooseRule and FunAppRule.
  *
  * @author Igor Konnov
  */
class DefaultValueFactory(rewriter: SymbStateRewriter) {
  def makeUpValue(state: SymbState, set: ArenaCell): SymbState = {
    makeUpValue(state, findElemType(set))
  }

  /**
    * Produce a default value that, for instance, can be used as a value when picking from an empty set.
    * @param state a symbolic state
    * @param cellType a cell type FinSetT(...)
    * @return a new symbolic state that contains the new value as the expression
    */
  def makeUpValue(state: SymbState, cellType: CellT): SymbState = {
    // TODO: introduce a cache for default values, otherwise there will be many identical copies
    cellType match {
      case IntT() =>
        rewriter.rewriteUntilDone(state.setRex(tla.int(0)))

      case BoolT() =>
        rewriter.rewriteUntilDone(state.setRex(tla.bool(false)))

      case ConstT() =>
        rewriter.rewriteUntilDone(state.setRex(tla.str("None")))

      case tupT @ TupleT(argTypes) =>
        var arena = state.arena.appendCell(tupT)
        val tuple = arena.topCell
        var newState = state.setArena(arena)
        for (argt <- argTypes) {
          newState = makeUpValue(newState, argt)
          val fieldCell = newState.asCell
          arena = newState.arena.appendHas(tuple, fieldCell)
          newState = newState.setArena(arena)
        }
        newState.setRex(tuple.toNameEx)

      case recT @ RecordT(_) =>
        var newState = state.appendArenaCell(recT)
        val recCell = newState.arena.topCell
        for (v <- recT.fields.values) {
          newState = makeUpValue(newState, v)
          val fieldCell = newState.asCell
          newState = newState.setArena(newState.arena.appendHas(recCell, fieldCell))
        }
        // create the domain and attach it to the record
        val (newArena, domain) = rewriter.recordDomainCache.getOrCreate(newState.arena, recT.fields.keySet)
        newState = newState.setArena(newArena.setDom(recCell, domain))
        newState.setRex(recCell.toNameEx)

      case tp @ FinSetT(_) => // {}
        var arena = state.arena.appendCell(tp)
        val set = arena.topCell
        state.setArena(arena).setRex(set.toNameEx).setArena(arena)

      case tp @ FunT(domT, cdmT) => // [x \in {} |-> {}]
        val relState = makeUpValue(state, FinSetT(TupleT(Seq(tp.argType, tp.resultType))))
        var arena = relState.arena.appendCell(tp)
        val funCell = arena.topCell
        arena = arena.setCdm(funCell, relState.asCell)
        relState.setArena(arena).setRex(funCell.toNameEx)

      case tp @ _ =>
        throw new RewriterException(s"Default values are not implemented for $tp")
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
}
