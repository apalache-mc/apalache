package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaArithOper, TlaFiniteSetOper}
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{OperEx, ValEx}
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Optimization for Cardinality(S) >= k, where k is constant. See [docs/smt/Cardinality.md].
 *
 * @author Igor Konnov
 */
class CardinalityConstRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickRule = new CherryPick(rewriter)

  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(ApalacheOper.constCard, OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, _), ValEx(
                      TlaInt(_)))) =>
        true

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(ApalacheOper.constCard, OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, setEx), ValEx(
                      TlaInt(thresholdBigInt)))) =>
        val threshold = thresholdBigInt.toInt
        var nextState = rewriter.rewriteUntilDone(state.setRex(setEx))
        val setCell = nextState.asCell
        val elems = nextState.arena.getHas(setCell)
        if (threshold <= 0) {
          nextState.setRex(tla.bool(true))
        } else if (elems.size < threshold) {
          nextState.setRex(tla.bool(false))
        } else {
          mkWitnesses(nextState, setCell, elems, threshold)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def mkWitnesses(state: SymbState, set: ArenaCell, elems: Seq[ArenaCell], threshold: Int): SymbState = {
    def solverAssert = rewriter.solverContext.assertGroundExpr(_)

    var nextState = state
    nextState = nextState.updateArena(_.appendCell(BoolT()))
    val emptyPred = nextState.arena.topCell
    solverAssert(tla.eql(emptyPred.toNameEx, tla.and(elems.map(e => tla.not(tla.in(e.toNameEx, set.toNameEx))): _*)))

    // pick `threshold` cells that will act as witnesses
    def pick(i: Int): ArenaCell = {
      nextState = pickRule.pick(set, nextState, emptyPred.toNameEx)
      nextState.asCell
    }

    // create an inequality constraint
    def cacheEq(pair: (ArenaCell, ArenaCell)): Unit = {
      nextState = rewriter.lazyEq.cacheOneEqConstraint(nextState, pair._1, pair._2)
    }

    // create the inequality predicate
    val witnesses = 1.to(threshold).map(pick).toList
    (witnesses cross witnesses).filter(p => p._1.id < p._2.id).foreach(cacheEq)
    val witnessesNotEq = OperEx(ApalacheOper.distinct, witnesses.map(_.toNameEx): _*)
    nextState = nextState.updateArena(_.appendCell(BoolT()))
    val pred = nextState.arena.topCell
    // either the set is empty and threshold <= 0, or all witnesses are not equal to each other
    val nonEmptyOrBelow = tla.or(tla.not(emptyPred.toNameEx), tla.bool(threshold <= 0))
    solverAssert(tla.eql(pred.toNameEx, tla.and(nonEmptyOrBelow, tla.or(emptyPred.toNameEx, witnessesNotEq))))

    // generate constraints
    nextState.setRex(pred.toNameEx)
  }
}
