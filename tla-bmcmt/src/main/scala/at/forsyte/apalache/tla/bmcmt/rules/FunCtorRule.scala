package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir._

/**
 * The new implementation of a function constructor that encodes a function f = [x \in S |-> e] the classical way:
 * f = {(a, b) : a \in S, b = e[a/x]. For efficiency, we are still carrying the domain set in a separate cell.
 *
 * @author Igor Konnov
 */
class FunCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.funDef, _*) => true
      case _                             => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaFunOper.funDef, mapEx, NameEx(varName), setEx) =>
        // note that we only have a single-argument case here, as Desugarer collapses multiple arguments into a tuple
        val funT = TlaType1.fromTypeTag(ex.typeTag).asInstanceOf[FunT1]
        rewriteFunCtor(state, funT, mapEx, varName, setEx)

      case _ =>
        throw new RewriterException(
            "%s is not applicable to %s"
              .format(getClass.getSimpleName, state.ex), state.ex)
    }
  }

  private def rewriteFunCtor(state: SymbState, funT1: FunT1, mapEx: TlaEx, varName: String, setEx: TlaEx) = {
    // rewrite the set expression into a memory cell
    var nextState = rewriter.rewriteUntilDone(state.setRex(setEx))
    val domainCell = nextState.asCell
    val funT = CellT.fromType1(funT1)
    val elemT = CellT.fromType1(funT1.arg)
    val resultT = CellT.fromType1(funT1.res)
    val domainCells = nextState.arena.getHas(domainCell)
    // find the type of the target expression and of the target set
    // unfold the set and map every potential element to a cell
    // actually, instead of mapping every cell to e, we map it to <<x, e>> to construct the relation
    val pairEx = tla
      .tuple(tla.name(varName).typed(funT1.arg), mapEx)
      .typed(TupT1(funT1.arg, funT1.res))

    val (afterMapState: SymbState, relationCells: Seq[ArenaCell]) =
      mapCells(nextState, pairEx, varName, setEx, domainCells)

    nextState = afterMapState
    // Add the cell for the set that stores the relation <<x, f[x]>>.
    nextState = nextState.updateArena(_.appendCell(funT))
    val funCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.appendCell(FinSetT(TupleT(Seq(elemT, resultT)))))
    val relation = nextState.arena.topCell
    val newArena = nextState.arena.appendHas(relation, relationCells: _*)
    // we do not store the function domain anymore, as it is easy to get the domain and the relation out of sync
//    nextState = nextState.setArena(newArena.setDom(funCell, domainCell))
    // For historical reasons, we are using cdm to store the relation, though it is not the co-domain.
    nextState = nextState.setArena(newArena.setCdm(funCell, relation))
    // require the relation to contain only those pairs whose argument actually belongs to the set

    // associate a value of the uninterpreted function with a cell
    def addCellCons(domElem: ArenaCell, relElem: ArenaCell): Unit = {
      val inDomain = tla.in(domElem.toNameEx, domainCell.toNameEx).typed(BoolT1())
      val inRelation = tla.in(relElem.toNameEx, relation.toNameEx).typed(BoolT1())
      val iff = tla.equiv(inDomain, inRelation).typed(BoolT1())
      rewriter.solverContext.assertGroundExpr(iff)
    }

    // add SMT constraints
    for ((domElem, relElem) <- domainCells zip relationCells)
      addCellCons(domElem, relElem)

    // that's it
    nextState.setRex(funCell.toNameEx)
  }

  private def mapCells(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx, oldCells: Seq[ArenaCell]) = {
    // similar to SymbStateRewriter.rewriteSeqUntilDone and SetFilterRule
    def process(st: SymbState, seq: Seq[ArenaCell]): (SymbState, Seq[TlaEx]) = {
      seq match {
        case Seq() =>
          (st, List())

        case cell :: tail =>
          val (ts: SymbState, nt: List[TlaEx]) = process(st, tail)
          val newBinding = Binding(ts.binding.toMap + (varName -> cell))
          val cellState = new SymbState(mapEx, ts.arena, newBinding)
          // add [cell/x]
          val ns = rewriter.rewriteUntilDone(cellState)
          (ns.setBinding(ts.binding), ns.ex :: nt) // reset binding and add the new expression in the head
      }
    }

    // compute mappings for all the cells (some of them may coincide, that's fine)
    val (newState: SymbState, newEs: Seq[TlaEx]) = process(state, oldCells)
    val newCells = newEs.map(newState.arena.findCellByNameEx)
    // keep the sequence of results as it is, as it is will be zipped by the function constructor
    (newState, newCells)
  }
}
