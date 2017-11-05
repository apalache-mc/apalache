package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * Implements the rules: SE-SET-MAP[1-2] and SE-FUN-CTOR[1-2].
  *
  * Since set map and function constructors have a lot in common, we implement them in the same class.
  *
  * @author Igor Konnov
  */
class SetMapAndFunCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.map, _*) => true
      case OperEx(TlaFunOper.funDef, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.funDef, mapEx, NameEx(varName), setEx) =>
        rewriteFunCtor(state, mapEx, varName, setEx)

      case OperEx(TlaSetOper.map, mapEx, NameEx(varName), setEx) =>
        rewriteSetMap(state, mapEx, varName, setEx)

      case _ =>
        throw new RewriterException("SetMapRule is not applicable")
    }
  }

  private def rewriteSetMap(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx) = {
    // rewrite the set expression into a memory cell
    val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(setEx))
    val oldSetCell = setState.arena.findCellByNameEx(setState.ex)
    // unfold the set and produce map every potential element to a cell
    val oldCells = setState.arena.getHas(oldSetCell)

    val (newState: SymbState, newCells: Seq[ArenaCell], elemType: CellT) =
      mapCells(setState, mapEx, varName, setEx, oldCells)

    // introduce a new set
    val arena = newState.arena.appendCell(FinSetT(elemType))
    val newSetCell = arena.topCell
    val newArena = newCells.foldLeft(arena)((a, e) => a.appendHas(newSetCell, e))

    // require each new cell to be in the new set iff the old cell was in the old set
    def addCellCons(oldCell: ArenaCell, newCell: ArenaCell): Unit = {
      val inNewSet = OperEx(TlaSetOper.in, newCell.toNameEx, newSetCell.toNameEx)
      val inOldSet = OperEx(TlaSetOper.in, oldCell.toNameEx, oldSetCell.toNameEx)
      val ifAndOnlyIf = OperEx(TlaOper.eq, inNewSet, inOldSet)
      newState.solverCtx.assertGroundExpr(ifAndOnlyIf)
    }

    // add SMT constraints
    for ((cell, pred) <- oldCells zip newCells)
      addCellCons(cell, pred)

    // that's it
    val finalState =
      newState.setTheory(CellTheory())
        .setArena(newArena).setRex(newSetCell.toNameEx)
    rewriter.coerce(finalState, state.theory)
  }

  private def rewriteFunCtor(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx) = {
    // rewrite the set expression into a memory cell
    val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(setEx))
    val domainCell = setState.arena.findCellByNameEx(setState.ex)
    // unfold the set and produce map every potential element to a cell
    val domainCells = setState.arena.getHas(domainCell)

    val (newState: SymbState, resultCells: Seq[ArenaCell], elemType: CellT) =
      mapCells(setState, mapEx, varName, setEx, domainCells)

    // introduce a new cell
    val arena = newState.arena.appendCell(FunT(domainCell.cellType, elemType))
    val funCell = arena.topCell
    val newArena = arena.setDom(funCell, domainCell)
    // associate a function constant with the function cell
    val _ = newArena.solverContext.getOrIntroCellFun(funCell)

    // associate a value of the uninterpreted function with a cell
    def addCellCons(argCell: ArenaCell, resultCell: ArenaCell): Unit = {
      val inDomain = OperEx(TlaSetOper.in, argCell.toNameEx, domainCell.toNameEx)
      val funEqResult = OperEx(TlaOper.eq,
        resultCell.toNameEx,
        OperEx(TlaFunOper.app, funCell.toNameEx, argCell.toNameEx)) // this will be translated as function application
      val inDomainImpliesResult = OperEx(TlaBoolOper.implies, inDomain, funEqResult)
      newState.solverCtx.assertGroundExpr(inDomainImpliesResult)
    }

    // add SMT constraints
    for ((cell, pred) <- domainCells zip resultCells)
      addCellCons(cell, pred)

    // that's it
    val finalState =
      newState.setTheory(CellTheory())
        .setArena(newArena).setRex(funCell.toNameEx)
    rewriter.coerce(finalState, state.theory)
  }

  private def mapCells(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx, oldCells: Seq[ArenaCell]) = {
    // similar to SymbStateRewriter.rewriteSeqUntilDone and SetFilterRule
    def process(st: SymbState, seq: Seq[ArenaCell]): (SymbState, Seq[TlaEx]) = {
      seq match {
        case Seq() =>
          (st, List())

        case (cell: ArenaCell) :: tail =>
          val (ts: SymbState, nt: List[TlaEx]) = process(st, tail)
          val newBinding = ts.binding + (varName -> cell)
          val cellState = new SymbState(mapEx, CellTheory(), ts.arena, newBinding, ts.solverCtx)
          // add [cell/x]
          val ns = rewriter.rewriteUntilDone(cellState)
          (ns.setBinding(ts.binding), ns.ex :: nt) // reset binding and add the new expression in the head
      }
    }

    // compute mappings for all the cells (some of them may coincide, that's fine)
    val (newState: SymbState, newEs: Seq[TlaEx]) = process(state, oldCells)
    val newCells = newEs.map(newState.arena.findCellByNameEx)
    // get the cell types
    val elemType =
      newCells.map(_.cellType).toSet.toList match {
        case List() => UnknownT()
        case hd :: List() => hd
        case list@_ => SumT(list)
      }

    (newState, newCells, elemType)
  }
}
