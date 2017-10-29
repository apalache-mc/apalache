package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter._
import at.forsyte.apalache.tla.bmcmt.rules.LogicConstRule

object SymbStateRewriter {
  abstract class RewritingResult
  case class Done(symbState: SymbState) extends RewritingResult
  case class Continue(symbState: SymbState) extends RewritingResult
  case class NoRule() extends RewritingResult
  case class StateSplit(numBranches: Int) extends RewritingResult

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
  private val rules = List(new LogicConstRule())

  def rewrite(state: SymbState, dir: SearchDirection): RewritingResult = {
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
}
