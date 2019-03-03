package at.forsyte.apalache.tla.bmcmt.search

import at.forsyte.apalache.tla.bmcmt.CheckerInput
import at.forsyte.apalache.tla.bmcmt.search.SearchStrategy.Command

class BfsStrategy(input: CheckerInput, stepsBound: Int) extends SearchStrategy {
  var stepNo = 0
  var terminate = false

  override def getCommand: Command = {
    if (terminate || stepNo > stepsBound) {
      SearchStrategy.Finish()
    } else if (stepNo == 0) {
      SearchStrategy.NextStep(stepNo, input.initTransitions.indices)
    } else {
      SearchStrategy.NextStep(stepNo, input.nextTransitions.indices)
    }
  }

  override def registerResponse(response: SearchStrategy.Response): Unit = {
    response match {
      case SearchStrategy.NextStepFired() => stepNo += 1
      case SearchStrategy.NextStepDisabled() => terminate = true
      case SearchStrategy.Backtracked() => () // nothing to do
    }
  }
}
