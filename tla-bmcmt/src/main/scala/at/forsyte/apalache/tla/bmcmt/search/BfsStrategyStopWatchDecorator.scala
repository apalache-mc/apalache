package at.forsyte.apalache.tla.bmcmt.search

import java.io.{FileWriter, PrintWriter, Writer}
import java.time.{Duration, LocalDateTime}

import at.forsyte.apalache.tla.bmcmt.search.SearchStrategy.{Finish, FinishOnDeadlock, NextStep}

/**
  * A decorator of a search strategy that measures the wall-clock time and records it in a CSV file.
  * This decorator is useful for plotting the time it takes BfsStrategy to explore the computations up to given length.
  *
  * The CSV contains the following fields: the step number, the total number of seconds elapsed since the start
  * till the end of the step, the additional nanoseconds till the end of the step. That is, if step 0 starts at time
  * instant A and step i ends at time instant B, then the first field contains i,
  * the second field contains seconds(B - A) and the third field contains nanoseconds(B - A) - seconds(B - A) * pow(10, 9).
  *
  * @author Igor Konnov
  */
class BfsStrategyStopWatchDecorator(strategy: SearchStrategy, filename: String) extends SearchStrategy {
  private var currentStep: Int = 0
  private var printWriter: Option[PrintWriter] = None
  private var startTime: LocalDateTime = LocalDateTime.now()

  override def getCommand: SearchStrategy.Command = {
    val command = strategy.getCommand
    command match {
      case NextStep(stepNo, _, _) =>
        if (stepNo == 0) {
          currentStep = 0
          // create a log file and add a header
          printWriter = Some(new PrintWriter(new FileWriter(filename, false)))
          printWriter.get.println("step,total_sec,nanosec_adjustment")
          // start the timer
          startTime = LocalDateTime.now()
        } else {
          appendCsvEntry()
          currentStep = stepNo
        }

      case Finish() | FinishOnDeadlock() =>
        appendCsvEntry()
        printWriter.get.close()
    }
    command
  }

  private def appendCsvEntry(): Unit = {
    val currentTime = LocalDateTime.now()
    val duration = Duration.between(startTime, currentTime)
    printWriter.get.println("%d,%d,%d".format(currentStep, duration.getSeconds, duration.getNano))
    printWriter.get.flush() // get the results as soon as possible
  }

  override def registerResponse(response: SearchStrategy.Response): Unit = {
    strategy.registerResponse(response)
  }
}
