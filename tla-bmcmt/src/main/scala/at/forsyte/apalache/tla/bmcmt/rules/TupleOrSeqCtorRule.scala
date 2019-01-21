package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-TPL-CTOR[1-2]. A tuple may be interpreted as a sequence, if it was properly type-annotated,
  * e.g., <<>> <: Seq(Int).
  *
  * @author Igor Konnov
  */
class TupleOrSeqCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
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

        // Get the resulting type from the type finder. It may happen to be a sequence!
        val resultT = rewriter.typeFinder.compute(state.ex, cells.map(_.cellType) :_*)

        // create the tuple or a sequence cell
        var arena = stateAfterElems.arena.appendCell(resultT)
        val tuple = arena.topCell

        // connect the cells to the tuple (or a sequence): the order of edges is important!
        arena = cells.foldLeft(arena)((a, e) => a.appendHas(tuple, e))

        val finalState = stateAfterElems.setArena(arena).setRex(tuple.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
