package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.ElemPtr
import at.forsyte.apalache.tla.lir.{OperEx, TlaType1}
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}

/**
 * Rewrites X \cup Y, that is, a union of two sets (not UNION). In the first encoding, we used a linear number of `in`
 * queries. However, this happens to be unsound, and we need a quadratic number of queries.
 *
 * @author
 *   Igor Konnov
 */
class SetCupRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.cup, _*) => true
      case _                          => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.cup, leftSet, rightSet) =>
        // rewrite the set expressions into memory cells
        var nextState = rewriter.rewriteUntilDone(state.setRex(leftSet))
        val leftSetCell = nextState.asCell
        nextState = rewriter.rewriteUntilDone(nextState.setRex(rightSet))
        val rightSetCell = nextState.asCell
        val leftElems = nextState.arena.getHasPtr(leftSetCell)
        val rightElems = nextState.arena.getHasPtr(rightSetCell)

        val common = Set(leftElems: _*).intersect(Set(rightElems: _*))
        val onlyLeft = Set(leftElems: _*).diff(common)
        val onlyRight = Set(rightElems: _*).diff(common)
        val allDistinct = common.toSeq ++ onlyLeft.toSeq ++ onlyRight.toSeq

        rewriter.solverContext.config.smtEncoding match {
          case SMTEncoding.Arrays =>
            // introduce a new set, encoded as a unconstrained array
            val newType = TlaType1.fromTypeTag(state.ex.typeTag)
            nextState = nextState.updateArena(_.appendCell(newType, isUnconstrained = true))
            val newSetCell = nextState.arena.topCell
            nextState = nextState.updateArena(_.appendHas(newSetCell, allDistinct: _*))

            // since newSet is initially unconstrained, we equate it to leftSet to add leftSet's elements to newSet
            rewriter.solverContext.assertGroundExpr(tla.eql(newSetCell.toBuilder, leftSetCell.toBuilder))
            // having added the elements of leftSet to newSet, we use SMT map to add rightSet's elements to newSet
            // we ensure that \forall e \in dom(newSet) : e \in newSet \iff e \in leftSet \lor e \in rightSet
            val smtMap = tla.smtMap(TlaBoolOper.or, rightSetCell.toBuilder, newSetCell.toBuilder)
            rewriter.solverContext.assertGroundExpr(smtMap)

            // that's it
            nextState.setRex(newSetCell.toBuilder)

          case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
            // introduce a new set
            val newType = TlaType1.fromTypeTag(state.ex.typeTag)
            nextState = nextState.updateArena(_.appendCell(newType))
            val newSetCell = nextState.arena.topCell
            nextState = nextState.updateArena(_.appendHas(newSetCell, allDistinct: _*))

            // require each cell to be in in the union iff it is exactly in its origin set
            def addOnlyCellCons(thisSet: ArenaCell, thisElemPtr: ElemPtr): Unit = {
              val thisElem = thisElemPtr.elem
              val inThis = tla.selectInSet(thisElem.toBuilder, thisSet.toBuilder)
              val inCup = tla.storeInSet(thisElem.toBuilder, newSetCell.toBuilder)
              val notInCup = tla.storeNotInSet(thisElem.toBuilder, newSetCell.toBuilder)
              rewriter.solverContext.assertGroundExpr(tla.ite(inThis, inCup, notInCup))
            }

            def addEitherCellCons(thisElemPtr: ElemPtr): Unit = {
              val thisElem = thisElemPtr.elem
              val inThis = tla.selectInSet(thisElem.toBuilder, leftSetCell.toBuilder)
              val inOther = tla.selectInSet(thisElem.toBuilder, rightSetCell.toBuilder)
              val inCup = tla.storeInSet(thisElem.toBuilder, newSetCell.toBuilder)
              val notInCup = tla.storeNotInSet(thisElem.toBuilder, newSetCell.toBuilder)
              rewriter.solverContext.assertGroundExpr(tla.ite(tla.or(inThis, inOther), inCup, notInCup))
            }

            // new implementation: as we are not using uninterpreted functions anymore, we do not have to care about
            // the problem described below.
            // Add equality constraints, e.g., for ({1} \ {1}) \cup {1}. Otherwise, we might require equal cells to be
            // inside and outside the resulting set
            //        val prodIter = new Prod2SeqIterator(leftElems, rightElems)
            //        val eqState = rewriter.lazyEq.cacheEqConstraints(rightState.setArena(arena), prodIter.toSeq)
            // bugfix: we have to compare the elements in both sets and thus to introduce a quadratic number of constraints
            // add SMT constraints
            onlyLeft.foreach(addOnlyCellCons(leftSetCell, _))
            onlyRight.foreach(addOnlyCellCons(rightSetCell, _))
            common.foreach(addEitherCellCons)

            // that's it
            nextState.setRex(newSetCell.toBuilder)

          case oddEncodingType =>
            throw new IllegalArgumentException(s"Unexpected SMT encoding of type $oddEncodingType")
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
