package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.SetOps
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFiniteSetOper
import at.forsyte.apalache.tla.lir.{IntT1, OperEx, SetT1, TlaEx}
import at.forsyte.apalache.tla.pp.TlaInputError

/**
 * Implements the Cardinality operator.
 *
 * @author
 *   Igor Konnov
 */
class CardinalityRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(TlaFiniteSetOper.cardinality, _) =>
        true

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFiniteSetOper.cardinality, setEx) =>
        val nextState = rewriter.rewriteUntilDone(state.setRex(setEx))
        val setCell = nextState.asCell
        setCell.cellType match {
          case CellTFrom(SetT1(_)) =>
            makeCardEquations(nextState, setCell)

          case tp =>
            throw new TlaInputError("Cardinality expected a finite set, found: " + tp, Some(state.ex.ID))
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def makeCardEquations(state: SymbState, set: ArenaCell): SymbState = {
    val (newState, nonDups) = new SetOps(rewriter).dedup(state, set)
    val (newArena, zero) = rewriter.intValueCache.getOrCreate(newState.arena, 0)
    var nextState = newState.setArena(newArena)

    def add(counter: TlaEx, isNonDup: ArenaCell): TlaEx = {
      tla.ite(isNonDup.toNameEx, tla.plus(tla.int(1), counter), counter)
    }

    val cardEx = nonDups.foldLeft(zero.toNameEx: TlaEx)(add)

    nextState = nextState.updateArena(_.appendCell(IntT1()))
    val cardinality = nextState.arena.topCell
    rewriter.solverContext.assertGroundExpr(tla.eql(cardinality.toNameEx, cardEx))

    nextState.setRex(cardinality.toNameEx)
  }
}
