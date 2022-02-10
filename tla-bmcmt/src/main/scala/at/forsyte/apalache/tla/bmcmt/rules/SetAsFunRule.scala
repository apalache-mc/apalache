package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.ApalacheOper

/**
 * Implements a rule for Apalache!SetAsFun.
 *
 * @author Igor Konnov
 */
class SetAsFunRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(ApalacheOper.setAsFun, _) => true
      case _                                => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(ApalacheOper.setAsFun, setEx) =>
        var nextState = rewriter.rewriteUntilDone(state.setRex(setEx))
        val setCell = nextState.asCell
        setEx.typeTag match {
          case Typed(SetT1(TupT1(keyType, valueType))) =>
            nextState = translateRelation(setCell, nextState)
            val rel = nextState.asCell
            // construct a cell for the function and attach the relation to it
            nextState = nextState.updateArena(_.appendCell(CellT.fromType1(FunT1(keyType, valueType))))
            val fun = nextState.arena.topCell
            nextState = nextState.updateArena(_.setCdm(fun, rel))
            nextState.setRex(fun.toNameEx)

          case tt =>
            throw new RewriterException("Unexpected type in SetAsFunRule: " + tt, state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def translateRelation(pairsSet: ArenaCell, state: SymbState): SymbState = {
    var nextState = state.updateArena(_.appendCell(pairsSet.cellType))
    // construct the relation cell `funRel` and add all cells from the original set `setCell`
    val funRel = nextState.arena.topCell
    val pairs = nextState.arena.getHas(pairsSet)
    nextState = nextState.updateArena(_.appendHas(funRel, pairs: _*))
    // however, iteratively restrict the membership, to enforce determinism
    for ((pair1, idx1) <- pairs.zipWithIndex) {
      val key1 = nextState.arena.getHas(pair1).head

      // ensure that a pair with the same key has not been included in the relation yet
      def keysDifferOrNotIncluded(pair2: ArenaCell): TlaEx = {
        val key2 = nextState.arena.getHas(pair2).head
        // pair2 \notin funRel
        val notInFunRel = tla.not(tla.apalacheSelectInSet(pair2.toNameEx, funRel.toNameEx))
        // key1 = key2
        nextState = rewriter.lazyEq.cacheOneEqConstraint(nextState, key1, key2)
        val keysEq = rewriter.lazyEq.cachedEq(key1, key2)
        // pair2 \notin funRel \/ key1 /= key2
        tla.or(notInFunRel, tla.not(keysEq))
      }

      val noDuplicateKeys = tla.and(pairs.slice(0, idx1).map(keysDifferOrNotIncluded): _*)
      // pair1 \in setCell
      val inSet = tla.apalacheSelectInSet(pair1.toNameEx, pairsSet.toNameEx)
      // pair1 \in funRel <=> pair1 \in setCell /\ notInPrefix
      val ite = tla.ite(tla.and(inSet, noDuplicateKeys), tla.apalacheStoreInSet(pair1.toNameEx, funRel.toNameEx),
          tla.apalacheStoreNotInSet(pair1.toNameEx, funRel.toNameEx))
      rewriter.solverContext.assertGroundExpr(ite)
    }

    nextState.setRex(funRel.toNameEx)
  }
}
