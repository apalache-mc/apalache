package at.forsyte.apalache.tla.bmcmt.rules.old

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Introduces a new function which is identical to the source function except the set of new values.
  * This is the pre-warp implementation.
  *
  * @author Igor Konnov
  */
class FunExceptRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new CherryPick(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.except, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.except, args@_*) =>
        val funEx = args.head
        val indexEs = args.tail.zipWithIndex.filter(_._2 % 2 == 0).map(_._1)
        val areIndicesTuples = indexEs map isPackedInTuple
        // first, unpack singleton tuples in indices, see the comment to the method
        val unpackedIndices = unpackSingletonIndices(indexEs)
        val valEs = args.tail.zipWithIndex.filter(_._2 % 2 == 1).map(_._1)
        assert(indexEs.size == valEs.size)

        // second, rewrite all the arguments
        val (groundState: SymbState, groundArgs: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), funEx +: (unpackedIndices ++ valEs))
        val funCell = groundState.arena.findCellByNameEx(groundArgs.head)
        val indexCells = groundArgs.slice(1, 1 + unpackedIndices.size)
          .map(groundState.arena.findCellByNameEx)
        val valueCells = groundArgs
          .slice(1 + unpackedIndices.size, 1 + unpackedIndices.size + valEs.size)
          .map(groundState.arena.findCellByNameEx)
        val updatePairs = indexCells.zip(valueCells) // ![j_i] = e_i

        // get domain and co-domain structure from the arena
        val dom = groundState.arena.getDom(funCell)
        val domCells = groundState.arena.getHas(dom)
        val cdm = groundState.arena.getCdm(funCell)
        val cdmElemType: types.CellT = findFunResultType(state, funCell, indexCells, valueCells, areIndicesTuples)

        // generate equality constraints for the domain elements and all the indices
        val eqState = rewriter.lazyEq.cacheEqConstraints(groundState, domCells cross indexCells)

        // create the new co-domain that includes the valueCells
        var arena = eqState.arena.appendCell(FinSetT(cdmElemType))
        val newCdm = arena.topCell

        // add all the elements from the old co-domain as well as the new values
        def addToNewCdm(a: Arena, c: ArenaCell) = a.appendHas(newCdm, c)

        arena = arena.getHas(cdm).foldLeft(arena)(addToNewCdm)
        arena = valueCells.foldLeft(arena)(addToNewCdm)
        // create a new function cell and wire it with the old domain and the new co-domain
        val funType = FunT(dom.cellType, cdmElemType)
        arena = arena.appendCell(funType)
        val newFunCell = arena.topCell
        arena = arena.setDom(newFunCell, dom).setCdm(newFunCell, newCdm)
        // introduce a new failure predicate
        arena = arena.appendCell(FailPredT())
        val failPred = arena.topCell
        // associate an uninterpreted function in SMT
        rewriter.solverContext.declareCellFun(newFunCell.name, funType.argType, funType.resultType)

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

        // finally, add the constraints in SMT
        val ok = tla.and(tla.not(failPred), tla.or(funUpdate))
        val notOk = tla.and(failPred, outsideDom)
        rewriter.solverContext.assertGroundExpr(tla.or(ok, notOk))

        val finalState = eqState
          .setArena(arena)
          .setTheory(CellTheory())
          .setRex(newFunCell)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def findFunResultType(state: SymbState, funCell: ArenaCell,
                                indexCells: Seq[ArenaCell], valueCells: Seq[ArenaCell],
                                areIndicesTuples: Seq[Boolean]) = {
    // make sure that the type finder is happy about the arguments
    def mkArgType(i: Int) = {
      val idx = i / 2
      if (i % 2 == 0) {
        if (areIndicesTuples(idx)) {
          indexCells(idx).cellType // it's a tuple already
        } else {
          TupleT(Seq(indexCells(idx).cellType)) // repack into a singleton tuple
        }
      } else {
        valueCells(idx).cellType
      }
    }

    val indexValueTypes = 0.until(2 * indexCells.size) map mkArgType
    val cdmElemType =
      rewriter.typeFinder.compute(state.ex, funCell.cellType +: indexValueTypes: _*) match {
        case FunT(FinSetT(_), resT) => resT
        case t@_ => throw new RewriterException("Expected a function type, found: " + t)
      }
    cdmElemType
  }

  // This is an important step. As we receive expressions from SANY, every index argument to EXCEPT
  // is always a tuple, even if we are using one-dimensional functions. For instance,
  // the expression [f EXCEPT ![1] = 2] will be represented as OperEx(TlaFunOper.except, f, <<1>>, 2).
  // Hence, we explicitly unpack singleton tuples. As for the non-singleton tuples, we keep them as is,
  // as this is the only reasonable way to access a function element with a multi-dimensional index without
  // introducing intermediate functions.
  private def unpackSingletonIndices(args: Seq[TlaEx]): Seq[TlaEx] = {
    def unpack(e: TlaEx) = e match {
      case OperEx(TlaFunOper.tuple, arg) =>
        arg // unpack
      case OperEx(TlaFunOper.tuple, _*) =>
        e // keep
      case _ =>
        // complain
        throw new RewriterException("Expected a tuple as a function index, found: " + e)
    }

    args map unpack
  }

  private def isPackedInTuple(e: TlaEx): Boolean = e match {
    case OperEx(TlaFunOper.tuple, args @ _*) => args.length != 1
    case _ => false
  }

}
