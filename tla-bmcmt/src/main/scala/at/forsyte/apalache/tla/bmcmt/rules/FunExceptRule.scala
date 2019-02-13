package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{CellT, FunT}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * Implements the rules: SE-FUN-UPD[1-4].
  *
  * @author Igor Konnov
  */
class FunExceptRule(rewriter: SymbStateRewriter) extends RewritingRule {

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
        // first, unpack singleton tuples in indices, see the comment to the method
        val unpackedIndices = unpackSingletonIndices(indexEs)
        val valEs = args.tail.zipWithIndex.filter(_._2 % 2 == 1).map(_._1)
        assert(indexEs.size == valEs.size)

        // second, rewrite all the arguments
        val (groundState: SymbState, groundArgs: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), funEx +: (unpackedIndices ++ valEs))
        val funCell = groundState.arena.findCellByNameEx(groundArgs.head)
        checkType(funCell.cellType)
        val indexCells = groundArgs.slice(1, 1 + unpackedIndices.size)
          .map(groundState.arena.findCellByNameEx)
        val valueCells = groundArgs
          .slice(1 + unpackedIndices.size, 1 + unpackedIndices.size + valEs.size)
          .map(groundState.arena.findCellByNameEx)
        // rewrite tuples <<j_i, e_i>> to cells
        val updatePairs = indexCells.zip(valueCells) // ![j_i] = e_i
        def mkPair(indexCell: ArenaCell, resCell: ArenaCell): TlaEx = tla.tuple(indexCell.toNameEx, resCell.toNameEx)
        val (stateAfterTuples, updateTuples) =
          rewriter.rewriteSeqUntilDone(groundState, updatePairs map (mkPair _).tupled)

        // get the function relation from the arena
        val relation = groundState.arena.getCdm(funCell)

        // filter the relation as follows:
        // { t \in F : t[1] != j_1 /\ ... /\ t[1] != j_k \/ t = <<j_1, e_1>> \/ ... \/ t = <<j_k, e_k>> }
        val boundVar = NameEx(s"_t${funEx.ID}")
        val argNeIndices = tla.and(indexCells map (c => tla.neql(tla.appFun(boundVar, tla.int(1)), c.toNameEx)) :_*)
        val pairEqNew = tla.or(updateTuples map (t => tla.eql(boundVar, t)) :_*)
        val filterEx = tla.filter(boundVar, relation.toNameEx, tla.or(argNeIndices, pairEqNew))

        var nextState = rewriter.rewriteUntilDone(stateAfterTuples.setRex(filterEx).setTheory(CellTheory()))
        val filteredRelation = nextState.asCell
        // Finally, add <<j_1, e_1>>, ..., <<j_k, e_k>> to filteredCell.
        // We are not using \cup here to avoid the equality constraints to be generated
        // TODO: this is not an issue anymore, use filter
        val filteredCells = nextState.arena.getHas(filteredRelation)
        nextState = nextState.appendArenaCell(filteredRelation.cellType)
        val resultRelation = nextState.arena.topCell
        val resultCells = filteredCells ++ updateTuples.map(nextState.arena.findCellByNameEx(_))
        nextState = nextState.setArena(nextState.arena.appendHas(resultRelation, resultCells))
        // require that the cells belong to the relation when the respective conditions hold true
        def solverAssert = rewriter.solverContext.assertGroundExpr _
        updateTuples foreach (t => solverAssert(tla.in(t, resultRelation)))
        filteredCells foreach (c => solverAssert(tla.equiv(tla.in(c, resultRelation), tla.in(c, filteredRelation))))

        // create new function
        nextState = nextState.appendArenaCell(funCell.cellType)
        val newFunCell = nextState.arena.topCell
        // not storing the domain anymore
//        val dom = nextState.arena.getDom(funCell)
//        nextState = nextState.setArena(nextState.arena.setDom(newFunCell, dom)
        nextState = nextState.setArena(nextState.arena.setCdm(newFunCell, resultRelation))

        val finalState = nextState
          .setTheory(CellTheory())
          .setRex(newFunCell)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  // This is an important step. As we receive expressions from SANY, every index argument to EXCEPT
  // is always a tuple]. For instance, the expression [f EXCEPT ![1] = 2] will be represented
  // as OperEx(TlaFunOper.except, f, <<1>>, 2). Hence, we explicitly unpack singleton tuples.
  // As for non-singleton tuples, they should be preprocessed.
  private def unpackSingletonIndices(args: Seq[TlaEx]): Seq[TlaEx] = {
    def unpack(e: TlaEx) = e match {
      case OperEx(TlaFunOper.tuple, arg) =>
        arg // unpack
      case OperEx(TlaFunOper.tuple, _*) =>
        throw new InternalCheckerError("TLA importer failed to preprocess a chained EXCEPT: " + e)
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

  private def checkType(cellType: CellT): Unit = {
    cellType match {
      case FunT(_, _) => () // o.k.
      case _ => throw new NotImplementedError(s"EXCEPT is not implemented for $cellType. Write a feature request.")
    }
  }
}
