package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, TupleT, UnknownT}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}

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
      case OperEx(TlaFunOper.tuple, elems@_*) =>
        // switch to cell theory
        val (stateAfterElems: SymbState, groundElems: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), elems)
        val cells = groundElems.map(stateAfterElems.arena.findCellByNameEx)
        // create the domain
        val (stateAfterRange: SymbState, range: Seq[TlaEx]) =
          mkDomain(stateAfterElems, cells.length)

        val stateAfterDomain = rewriter.rewriteUntilDone(stateAfterRange
          .setTheory(CellTheory())
          .setRex(tla.enumSet(range: _*)))
        val dom = stateAfterDomain.arena.findCellByNameEx(stateAfterDomain.ex)
        // create the co-domain
        var arena = stateAfterDomain.arena.appendCell(FinSetT(UnknownT()))
        val cdm = arena.topCell
        // add the cells to the co-domain
        arena = cells.foldLeft(arena)((a, e) => a.appendHas(cdm, e))
        def addIn(elemEx: TlaEx): Unit = {
          stateAfterDomain.solverCtx.assertGroundExpr(tla.in(elemEx, cdm.toNameEx))
        }
        groundElems.foreach(addIn)
        // create the tuple cell
        arena = arena.appendCell(TupleT(cells.map(_.cellType)))
        val tuple = arena.topCell
        arena = arena.setDom(tuple, dom).setCdm(tuple, cdm)
        // associate a function constant with the tuple
        val _ = arena.solverContext.getOrIntroCellFun(tuple)
        // connect the values to the indices
        def setVal(indexAndElem: (TlaEx, TlaEx)): Unit = {
          val funapp = tla.appFun(tuple.toNameEx, indexAndElem._1)
          stateAfterDomain.solverCtx.assertGroundExpr(tla.eql(funapp, indexAndElem._2))
        }
        range.zip(groundElems).foreach(setVal)

        val finalState =
          stateAfterDomain.setArena(arena).setRex(tuple.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("TupleCtorRule is not applicable")
    }
  }

  private def mkDomain(state: SymbState, count: Int): (SymbState, Seq[TlaEx]) = {
    val range = Range(1, count + 1).map(i => ValEx(TlaInt(i)))
    rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), range)
  }
}
