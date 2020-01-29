package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFiniteSetOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}


/**
  * Implements the Cardinality operator.
  *
  * @author Igor Konnov
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
        var nextState = rewriter.rewriteUntilDone(state.setRex(setEx).setTheory(CellTheory()))
        val setCell = nextState.asCell
        val elems = nextState.arena.getHas(setCell)
        nextState = makeCardEquations(nextState, setCell, elems)
        rewriter.coerce(nextState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def makeCardEquations(state: SymbState, set: ArenaCell, cells: Seq[ArenaCell]): SymbState = {
    var arena = state.arena // WARNING: it is updated in many places in this function

    def solverAssert = rewriter.solverContext.assertGroundExpr(_)

    def eqToOther(thisCell: ArenaCell, otherCell: ArenaCell): TlaEx = {
      tla.and(tla.in(otherCell, set), rewriter.lazyEq.safeEq(thisCell, otherCell))
    }

    // Generate a series of equations for cardinalities. Again, there are O(N^2) constraints. Cardinalities are hard!
    def mkEq(counted: Seq[ArenaCell], counter: ArenaCell, notCounted: Seq[ArenaCell]): ArenaCell = {
      notCounted match {
        case Nil => counter // all counted!

        case hd +: tl =>
          arena = arena.appendCell(IntT())
          val newCounter = arena.topCell
          // newCounter = counter if hd \notin set \/ \E c \in counted: hd = c /\ c \in set
          arena = arena.appendCell(BoolT())
          val beforePred = arena.topCell
          val beforeEx = tla.or(tla.notin(hd, set), tla.or(counted.map(eqToOther(hd, _)) :_*))
          solverAssert(tla.eql(beforePred, beforeEx))
          // newCounter = counter + 1 otherwise
          solverAssert(tla.eql(newCounter,
            tla.ite(beforePred, counter, tla.plus(tla.int(1), counter))))
          mkEq(hd +: counted, newCounter, tl)
      }
    }

    var nextState = state
    // Cache equality constraints. There are N^2 / 2 of them. Yes, cardinalities are expensive.
    for (l <- cells) {
      for (r <- cells) {
        if (l.id < r.id) {
          nextState = rewriter.lazyEq.cacheOneEqConstraint(nextState, l, r)
        }
      }
    }
    arena = nextState.arena

    // generate constraints
    arena = arena.appendCell(IntT())
    val initialCounter = arena.topCell
    solverAssert(tla.eql(initialCounter, tla.int(0)))
    val finalCounter = mkEq(Seq(), initialCounter, cells)

    nextState.setArena(arena).setRex(finalCounter).setTheory(CellTheory())
  }
}
