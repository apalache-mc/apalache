package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaArithOper, TlaFiniteSetOper}
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{BoolT1, OperEx, ValEx}
import at.forsyte.apalache.tla.types.{tlaU => tla}

/**
 * Optimization for Cardinality(S) >= k, where k is constant. See [docs/smt/Cardinality.md].
 *
 * @author
 *   Igor Konnov
 */
class CardinalityConstRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickRule = new CherryPick(rewriter)

  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(ApalacheOper.constCard,
              OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, _), ValEx(TlaInt(_)))) =>
        true

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(ApalacheOper.constCard,
              OperEx(TlaArithOper.ge, OperEx(TlaFiniteSetOper.cardinality, setEx), ValEx(TlaInt(thresholdBigInt)))) =>
        val threshold = thresholdBigInt.toInt
        val nextState = rewriter.rewriteUntilDone(state.setRex(setEx))
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

  private def mkWitnesses(
      state: SymbState,
      set: ArenaCell,
      elems: Seq[ArenaCell],
      threshold: Int): SymbState = {
    def solverAssert = rewriter.solverContext.assertGroundExpr(_)

    var nextState = state
    nextState = nextState.updateArena(_.appendCell(BoolT1))
    val emptyPred = nextState.arena.topCell
    solverAssert(tla.eql(emptyPred.toBuilder,
            tla.and(elems.map(e => tla.not(tla.selectInSet(e.toBuilder, set.toBuilder))): _*)))

    // pick `threshold` cells that will act as witnesses
    def pick(): ArenaCell = {
      nextState = pickRule.pick(set, nextState, emptyPred.toBuilder)
      nextState.asCell
    }

    // create an inequality constraint
    def cacheEq(pair: (ArenaCell, ArenaCell)): Unit = {
      nextState = rewriter.lazyEq.cacheOneEqConstraint(nextState, pair._1, pair._2)
    }

    // create the inequality predicate
    val witnesses = List.fill(threshold)(pick())
    (witnesses.cross(witnesses)).filter(p => p._1.id < p._2.id).foreach(cacheEq)
    val witnessesNotEq = tla.distinct(witnesses.map(_.toBuilder): _*)
    nextState = nextState.updateArena(_.appendCell(BoolT1))
    val pred = nextState.arena.topCell
    // either the set is empty and threshold <= 0, or all witnesses are not equal to each other
    val nonEmptyOrBelow = tla.or(tla.not(emptyPred.toBuilder), tla.bool(threshold <= 0))
    solverAssert(tla.eql(pred.toBuilder, tla.and(nonEmptyOrBelow, tla.or(emptyPred.toBuilder, witnessesNotEq))))

    // generate constraints
    nextState.setRex(pred.toBuilder)
  }
}
