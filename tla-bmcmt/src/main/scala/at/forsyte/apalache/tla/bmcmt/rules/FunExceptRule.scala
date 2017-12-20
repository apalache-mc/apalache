package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, FunT}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-FUN-UPD[1-4].
  *
  * @author Igor Konnov
  */
class FunExceptRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new PickFromAndFunMerge(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.except, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.except, args@_*) =>
        // simplify all the arguments first
        val (groundState: SymbState, groundArgs: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), args)

        // the function always comes first
        val funCell = groundState.arena.findCellByNameEx(groundArgs.head)
        // then the indices and righthand-side expressions interleaved
        val argCells = groundArgs.tail.map(groundState.arena.findCellByNameEx)
        val indexCells = argCells.zipWithIndex.filter(_._2 % 2 == 0).map(_._1) // pick the even indices (starting with 0)
      val valueCells = argCells.zipWithIndex.filter(_._2 % 2 == 1).map(_._1) // pick the odd indices (starting with 0)
        assert(indexCells.length == valueCells.length)
        val updatePairs = indexCells.zip(valueCells) // ![j_i] = e_i

        // get domain and co-domain structure from the arena
        val dom = groundState.arena.getDom(funCell)
        val domCells = groundState.arena.getHas(dom)
        val cdm = groundState.arena.getCdm(funCell)

        // generate equality constraints for the domain elements and all the indices
        val eqState = rewriter.lazyEq.cacheEqConstraints(groundState, domCells cross indexCells)

        // induce the new type of the co-domain cells
        val cdmElemType = cdm.cellType match {
          case FinSetT(elemType) =>
            val problemType = valueCells.find(!_.cellType.comparableWith(elemType))
            if (problemType.isDefined) {
              throw new RewriterException("Type error in %s: updating a function of type %s with a cell of type"
                .format(funCell.cellType, problemType.get))
            }
            elemType

          // TODO: we might want to extend the co-domain type a bit, when adding a tuple or a record

          case _ =>
            throw new RewriterException("Unexpected type of function co-domain in function update: %s"
              .format(cdm.cellType))
        }

        // create the new co-domain that includes the valueCells
        var arena = eqState.arena.appendCell(FinSetT(cdmElemType))
        val newCdm = arena.topCell

        // add all the elements from the old co-domain as well as the new values
        def addToNewCdm(a: Arena, c: ArenaCell) = a.appendHas(newCdm, c)

        arena = arena.getHas(cdm).foldLeft(arena)(addToNewCdm)
        arena = valueCells.foldLeft(arena)(addToNewCdm)
        // create a new function cell and wire it with the old domain and the new co-domain
        arena = arena.appendCell(FunT(dom.cellType, cdmElemType))
        val newFunCell = arena.topCell
        arena = arena.setDom(newFunCell, dom).setCdm(newFunCell, newCdm)
        val _ = arena.solverContext.getOrIntroCellFun(newFunCell) // create an uninterpreted function in SMT

        // add the update constraints
        def eachDomElem(domElem: ArenaCell) = {
          def onHit(index: ArenaCell, newValue: ArenaCell): TlaEx = {
            val hit = rewriter.lazyEq.safeEq(index, domElem)

            def update(c: ArenaCell): TlaEx = tla.eql(tla.appFun(newFunCell, c), newValue)

            tla.and(hit, update(domElem), update(index))
          }

          val hitsUpdate = updatePairs.map(p => onHit(p._1, p._2))

          def noHit(index: ArenaCell) = {
            tla.not(rewriter.lazyEq.safeEq(index, domElem))
          }

          val noHitFound = tla.and(indexCells.map(noHit): _*)
          val unchanged = tla.eql(tla.appFun(newFunCell, domElem), tla.appFun(funCell, domElem))
          // there is an index that hits, or there is no such index, and no update is needed
          val notIn = tla.not(tla.in(domElem, dom)) // if the cell is outside the domain, we don't care
          tla.or(notIn +: tla.and(noHitFound, unchanged) +: hitsUpdate: _*)
        }

        val funUpdate = tla.and(domCells.map(eachDomElem): _*)

        // flag a failure when there is an index outside the function domain
        def existsIndexOutside(index: ArenaCell): TlaEx = {
          def eachElem(domElem: ArenaCell) = {
            tla.and(tla.not(tla.eql(index, domElem)), tla.not(tla.in(domElem, dom)))
          }

          tla.and(domCells.map(eachElem): _*)
        }

        val outsideDom = tla.or(indexCells.map(existsIndexOutside): _*)
        val eqFailure = tla.eql(funCell, eqState.arena.cellFailure())

        // finally, add the constraints in SMT
        eqState.solverCtx.assertGroundExpr(tla.or(funUpdate))//, tla.and(outsideDom, eqFailure)))

        val finalState = eqState
          .setArena(arena)
          .setTheory(CellTheory())
          .setRex(newFunCell)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("FunExceptRule is not applicable")
    }
  }

}
