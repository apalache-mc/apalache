package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, IntT, TupleT, UnknownT}
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
        // TODO: do not use unknown here, as the solver will use it against you
        var arena = stateAfterDomain.arena.appendCell(FinSetT(UnknownT()))
        val cdm = arena.topCell
        // add the cells to the co-domain
        arena = cells.foldLeft(arena)((a, e) => a.appendHas(cdm, e))
        def addIn(elemEx: TlaEx): Unit = {
          rewriter.solverContext.assertGroundExpr(tla.in(elemEx, cdm.toNameEx))
        }
        groundElems.foreach(addIn)
        // create the tuple cell
        arena = arena.appendCell(TupleT(cells.map(_.cellType)))
        val tuple = arena.topCell
        arena = arena.setDom(tuple, dom).setCdm(tuple, cdm)
        // Associate a function constant with the tuple.
        // As tuples can be extended, we do not specify types explicitly.
        val _ = rewriter.solverContext.declareCellFun(tuple.toNameEx.name, IntT(), UnknownT())
        // connect the values to the indices
        def setVal(indexAndElem: (TlaEx, TlaEx)): Unit = {
          val funapp = tla.appFun(tuple.toNameEx, indexAndElem._1)
          // TODO: here we hit an inherent problem with types and sorts.
          // Since we need a single sort for a result type, we need a different presentation for tuples
          rewriter.solverContext.assertGroundExpr(tla.eql(funapp, indexAndElem._2))
        }
        range.zip(groundElems).foreach(setVal)

        val finalState =
          stateAfterDomain.setArena(arena).setRex(tuple.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def mkDomain(state: SymbState, count: Int): (SymbState, Seq[TlaEx]) = {
    val range = Range(1, count + 1).map(i => ValEx(TlaInt(i)))
    rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), range)
  }
}
