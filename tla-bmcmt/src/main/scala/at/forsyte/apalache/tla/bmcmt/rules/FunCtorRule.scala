package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * Implements the rules: SE-SET-MAP[1-2] and SE-FUN-CTOR[1-2].
  *
  * Since set map and function constructors have a lot in common, we implement them in the same class.
  *
  * @author Igor Konnov
  */
class FunCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.funDef, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.funDef, mapEx, NameEx(varName), setEx) =>
        // TODO: add support for multiple arguments
        rewriteFunCtor(state, mapEx, varName, setEx)

      case _ =>
        throw new RewriterException("%s is not applicable to %s"
          .format(getClass.getSimpleName, state.ex))
    }
  }

  private def rewriteFunCtor(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx) = {
    // rewrite the set expression into a memory cell
    val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(setEx))
    val domainCell = setState.arena.findCellByNameEx(setState.ex)
    val elemT = domainCell.cellType match {
      case FinSetT(et) => et
      case t@_ => throw new RewriterException("Expected a finite set, found: " + t)
    }
    // find the type of the target expression and of the target set
    val resultT = rewriter.typeFinder.computeRec(mapEx)
    val funT =
      rewriter.typeFinder
        .compute(state.ex, resultT, elemT, domainCell.cellType)
        .asInstanceOf[FunT]
    // unfold the set and map every potential element to a cell
    val domainCells = setState.arena.getHas(domainCell)

    val (newState: SymbState, resultCells: Seq[ArenaCell]) =
      mapCells(setState, mapEx, varName, setEx, domainCells)

    // introduce a co-domain cell
    var arena = newState.arena.appendCell(funT)
    val funCell = arena.topCell
    arena = arena.appendCell(FinSetT(resultT)) // co-domain is a finite set of type elemType
    val codomainCell = arena.topCell
    arena = arena.setDom(funCell, domainCell).setCdm(funCell, codomainCell)
    arena = resultCells.foldLeft(arena)((a, e) => a.appendHas(codomainCell, e))
    // associate a function constant with the function cell
    rewriter.solverContext.declareCellFun(funCell.name, funT.argType, funT.resultType)

    // associate a value of the uninterpreted function with a cell
    def addCellCons(argCell: ArenaCell, resultCell: ArenaCell): Unit = {
      val inDomain = tla.in(argCell, domainCell)
      val funEqResult = tla.eql(resultCell, tla.appFun(funCell, argCell)) // this is translated as function application
      val inDomainImpliesResult = tla.impl(inDomain, funEqResult)
      rewriter.solverContext.assertGroundExpr(inDomainImpliesResult)
      // the result unconditionally belongs to the co-domain
      rewriter.solverContext.assertGroundExpr(tla.in(resultCell, codomainCell))
    }

    // add SMT constraints
    for ((cell, pred) <- domainCells zip resultCells)
      addCellCons(cell, pred)

    // that's it
    val finalState =
      newState.setTheory(CellTheory())
        .setArena(arena).setRex(funCell.toNameEx)
    rewriter.coerce(finalState, state.theory)
  }

  private def mapCells(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx, oldCells: Seq[ArenaCell]) = {
    // similar to SymbStateRewriter.rewriteSeqUntilDone and SetFilterRule
    def process(st: SymbState, seq: Seq[ArenaCell]): (SymbState, Seq[TlaEx]) = {
      seq match {
        case Seq() =>
          (st, List())

        case cell :: tail =>
          val (ts: SymbState, nt: List[TlaEx]) = process(st, tail)
          val newBinding = ts.binding + (varName -> cell)
          val cellState = new SymbState(mapEx, CellTheory(), ts.arena, newBinding)
          // add [cell/x]
          val ns = rewriter.rewriteUntilDone(cellState)
          (ns.setBinding(ts.binding), ns.ex :: nt) // reset binding and add the new expression in the head
      }
    }

    // compute mappings for all the cells (some of them may coincide, that's fine)
    val (newState: SymbState, newEs: Seq[TlaEx]) = process(state, oldCells)
    val newCells = newEs.map(newState.arena.findCellByNameEx)
    // keep the sequence of results as it is, as it is be zipped by the function constructor
    (newState, newCells)
  }
}
