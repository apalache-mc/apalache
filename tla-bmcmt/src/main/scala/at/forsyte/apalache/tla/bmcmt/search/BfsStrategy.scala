package at.forsyte.apalache.tla.bmcmt.search

import at.forsyte.apalache.tla.bmcmt.CheckerInput
import at.forsyte.apalache.tla.bmcmt.search.SearchStrategy.Command

class BfsStrategy(input: CheckerInput, stepsBound: Int) extends SearchStrategy {
  var stepNo = 0
  var deadlock = false

  override def getCommand: Command = {
    if (stepNo > stepsBound) {
      SearchStrategy.Finish()
    } else if (deadlock) {
      SearchStrategy.FinishOnDeadlock()
    } else if (stepNo == 0) {
      SearchStrategy.NextStep(stepNo, input.initTransitions.indices)
    } else {
      SearchStrategy.NextStep(stepNo, input.nextTransitions.indices)
    }
  }

  override def registerResponse(response: SearchStrategy.Response): Unit = {
    response match {
      case SearchStrategy.NextStepFired()    => stepNo += 1
      case SearchStrategy.NextStepDisabled() => deadlock = true
      case SearchStrategy.Backtracked()      => () // nothing to do
    }
  }
}
