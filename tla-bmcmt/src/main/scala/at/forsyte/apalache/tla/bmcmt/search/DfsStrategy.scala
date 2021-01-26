package at.forsyte.apalache.tla.bmcmt.search

import at.forsyte.apalache.tla.bmcmt.CheckerInput
import at.forsyte.apalache.tla.bmcmt.search.SearchStrategy.{
  BacktrackOnce,
  Command,
  Finish
}
import com.typesafe.scalalogging.LazyLogging

import scala.util.Random

class DfsStrategy(input: CheckerInput, stepsBound: Int, randomize: Boolean)
    extends SearchStrategy
    with LazyLogging {
  var stepNo = 0
  var terminate = false
  var unexploredIndices: Seq[Seq[Int]] = Seq()

  override def getCommand: Command = {
    if (terminate) {
      SearchStrategy.Finish()
    } else if (stepNo > stepsBound) {
      logger.debug(s"DFS: backtrack, bound reached")
      unexploredIndices = Seq() +: unexploredIndices // add an empty sequence for the response handler to pop of the stack
      BacktrackOnce()
    } else if (stepNo == 0) {
      if (unexploredIndices.isEmpty) {
        val allIndices = shuffleIfNeeded(input.initTransitions.indices)
        unexploredIndices = Seq(allIndices.tail)
        // start with the head
        val hd = allIndices.head
        logger.debug(s"DFS: step $stepNo, transition $hd")
        SearchStrategy.NextStep(stepNo, Seq(hd))
      } else {
        assert(unexploredIndices.length == 1)
        if (unexploredIndices.head.isEmpty) {
          // all transitions at level 0 were enumerated, which means that all bounded paths were enumerated
          Finish()
        } else {
          val (hd, tl) =
            (unexploredIndices.head.head, unexploredIndices.head.tail)
          unexploredIndices = Seq(tl)
          // explore the next transition
          logger.debug(s"DFS: step $stepNo, transition $hd")
          SearchStrategy.NextStep(stepNo, Seq(hd), popContext = true)
        }
      }
    } else { // step > 0
      if (unexploredIndices.length - 1 < stepNo) {
        // explore all transitions at this depth
        val allIndices = shuffleIfNeeded(input.nextTransitions.indices)
        unexploredIndices = allIndices.tail +: unexploredIndices
        // start with the head
        val hd = allIndices.head
        logger.debug(s"DFS: step $stepNo, transition $hd")
        SearchStrategy.NextStep(stepNo, Seq(hd))
      } else {
        val unexplored = unexploredIndices.head
        if (unexplored.isEmpty) {
          // all transitions at this level were enumerated, backtrack
          logger.debug(s"DFS: backtrack from step $stepNo")
          BacktrackOnce()
        } else {
          val (hd, tl) = (unexplored.head, unexplored.tail)
          unexploredIndices = tl +: unexploredIndices.tail
          // explore the i-th transition
          logger.debug(s"DFS: step $stepNo, transition $hd")
          SearchStrategy.NextStep(stepNo, Seq(hd), popContext = true)
        }
      }
    }
  }

  override def registerResponse(response: SearchStrategy.Response): Unit = {
    response match {
      case SearchStrategy.NextStepFired() =>
        logger.debug(s"DFS response: fired")
        stepNo += 1

      case SearchStrategy.Backtracked() =>
        logger.debug(s"DFS response: backtracked")
        stepNo -= 1
        unexploredIndices = unexploredIndices.tail

      case SearchStrategy.NextStepDisabled() =>
        logger.debug(s"DFS response: disabled")
        () // nothing to do, just continue at this level
    }
  }

  private def shuffleIfNeeded(transitions: Seq[Int]): Seq[Int] = {
    if (randomize) {
      Random.shuffle(transitions)
    } else {
      transitions
    }
  }
}
