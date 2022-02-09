package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.{FunT1, TlaEx}

/**
 * Implements f[x] for: functions, records, and tuples.
 *
 * @author
 *   Rodrigo Otoni
 */
class FunAppRuleWithArrays(rewriter: SymbStateRewriter) extends FunAppRule(rewriter) {

  // TODO: override applyRecord, applyTuple, and applySeq later

  override protected def applyFun(state: SymbState, funCell: ArenaCell, argEx: TlaEx): SymbState = {
    val funT1 = funCell.cellType.toTlaType1.asInstanceOf[FunT1]
    val elemT = CellT.fromType1(funT1.res)

    var nextState = rewriter.rewriteUntilDone(state.setRex(argEx))
    val argCell = nextState.asCell

    val relationCell = nextState.arena.getCdm(funCell)
    val relationElems = nextState.arena.getHas(relationCell)
    val nElems = relationElems.size

    nextState = nextState.updateArena(_.appendCell(elemT, isUnconstrained = true)) // The cell will be unconstrained
    val res = nextState.arena.topCell

    // If the domain is non-empty we query the array representing the function
    // if the domain is empty we return an unconstrained value
    if (nElems > 0) {
      // The SMT constraints are produced here
      val select = tla.apalacheSelectInFun(argCell.toNameEx, funCell.toNameEx)
      val eql = tla.eql(res.toNameEx, select)
      rewriter.solverContext.assertGroundExpr(eql)

      // The cell metadata is propagated here
      for (elem <- relationElems) {
        val elemTuple = nextState.arena.getHas(elem)
        assert(elemTuple.size == 2) // elem should always have only edges to <arg,res>
        val elemArg = elemTuple(0)
        val elemRes = elemTuple(1)
        if (elemArg == argCell) {
          nextState = nextState.updateArena(_.appendHasNoSmt(res, nextState.arena.getHas(elemRes): _*))

          if (elemRes.cellType.isInstanceOf[FunT] | elemRes.cellType.isInstanceOf[FinFunSetT]) {
            nextState = nextState.updateArena(_.setDom(res, nextState.arena.getDom(elemTuple.tail.head)))
            nextState = nextState.updateArena(_.setCdm(res, nextState.arena.getCdm(elemTuple.tail.head)))
          } else if (elemRes.cellType.isInstanceOf[RecordT]) {
            // Records do not contain cdm metadata
            nextState = nextState.updateArena(_.setDom(res, nextState.arena.getDom(elemTuple.tail.head)))
          }
        }
      }
    }

    nextState.setRex(res.toNameEx)
  }
}
