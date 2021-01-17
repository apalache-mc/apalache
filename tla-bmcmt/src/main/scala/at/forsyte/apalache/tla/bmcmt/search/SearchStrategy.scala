package at.forsyte.apalache.tla.bmcmt.search

import at.forsyte.apalache.tla.bmcmt.search.SearchStrategy.{Command, Response}

/**
  * An abstract behavior of a search strategy that defines, whether to merge transitions together (BFS-like),
  * or explore them one-by-one (DFS-like), or do something else. The search strategies are stateful, assuming
  * that there is a stack of transitions. They make their decisions based on the step number and the transition number.
  *
  * @author Igor Konnov
  */
@deprecated
trait SearchStrategy {
  def getCommand: Command

  def registerResponse(response: Response)
}

object SearchStrategy {
  abstract class Command
  case class NextStep(stepNo: Int, transitions: Seq[Int], popContext: Boolean = false) extends Command
  case class BacktrackOnce() extends Command
  case class Finish() extends Command
  case class FinishOnDeadlock() extends Command

  abstract class Response
  case class NextStepFired() extends Response
  case class NextStepDisabled() extends Response
  case class Backtracked() extends Response
}
