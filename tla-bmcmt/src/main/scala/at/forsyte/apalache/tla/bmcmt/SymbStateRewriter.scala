package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter._
import at.forsyte.apalache.tla.bmcmt.rules.{AndRule, LogicConstRule, OrRule}

object SymbStateRewriter {

  sealed abstract class RewritingResult

  case class Done(symbState: SymbState) extends RewritingResult

  case class Continue(symbState: SymbState) extends RewritingResult

  case class NoRule() extends RewritingResult

  /**
    * As some rules may produce several states, we have to specify a direction.
    */
  abstract class SearchDirection

  /**
    * Assume that no branching is needed and rewrite as much as possible.
    */
  case class FastForward() extends SearchDirection

  /**
    * Go forward a chosen branch
    *
    * @param no the branch number (starts with 0)
    */
  case class FollowBranch(no: Int) extends SearchDirection

}

/**
  * This class rewrites a symbolic state.
  * This is the place where all the action regarding the operational semantics is happening.
  */
class SymbStateRewriter {
  private val rules = List(new LogicConstRule(this), new OrRule(this), new AndRule(this))

  def rewriteOnce(state: SymbState, dir: SearchDirection): RewritingResult = {
    state.rex match {
      case PredRex(_) =>
        Done(state)

      case TlaRex(_) =>
        // TODO: use something more efficient than just a linear search
        rules.find(r => r.isApplicable(state)) match {
          case Some(r) =>
            Continue(r.apply(state, dir))

          case None =>
            NoRule()
        }
    }
  }

  /**
    * Rewrite one expression until converged, or no rule applies.
    *
    * @param state a state to rewrite
    * @return the final state
    * @throws RewriterException if no rule applies
    */
  def rewriteUntilDone(state: SymbState): SymbState = {
    rewriteOnce(state, FastForward()) match {
      case Done(nextState) =>
        // converged to the normal form
        nextState

      case Continue(nextState) =>
        // more translation steps are needed
        // TODO: place a guard on the number of recursive calls
        rewriteUntilDone(nextState)

      case NoRule() =>
        // no rule applies, a problem in the tool?
        throw new RewriterException("No rule applies")
    }
  }

  /**
    * Rewrite all expressions in a sequence.
    *
    * @param state a state to start with
    * @param rexes a sequence of expressions to rewrite
    * @return a pair (the old state in a new context, the rewritten expressions)
    */
  def rewriteSeqUntilDone(state: SymbState, rexes: Seq[Rex]): (SymbState, Seq[Rex]) = {
    def process(st: SymbState, seq: Seq[Rex]): (SymbState, Seq[Rex]) = {
      seq match {
        case Seq() =>
          (st, List())

        case r :: tail =>
          val (ts: SymbState, nt: List[Rex]) = process(st, tail)
          val ns = rewriteUntilDone(new SymbState(r, ts.arena, ts.binding, ts.solverCtx))
          (ns, ns.rex :: nt)
      }
    }

    val pair = process(state, rexes.reverse)
    (pair._1.setRex(state.rex), pair._2)
  }
}
