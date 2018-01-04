package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.TupleT
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-TPL-CTOR[1-2].
  *
  * @author Igor Konnov
  */
class TupleCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.tuple, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.tuple, elems @ _*) =>
        // switch to cell theory
        val (stateAfterElems: SymbState, groundElems: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), elems)
        val cells = groundElems.map(stateAfterElems.arena.findCellByNameEx)

        // create the tuple cell
        var arena = stateAfterElems.arena.appendCell(TupleT(cells.map(_.cellType)))
        val tuple = arena.topCell

        // connect the cells to the tuple: the order of edges is important!
        arena = cells.foldLeft(arena)((a, e) => a.appendHas(tuple, e))

        val finalState = stateAfterElems.setArena(arena).setRex(tuple.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
