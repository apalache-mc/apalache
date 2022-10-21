package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.options.SourceOption.FileSource
import at.forsyte.apalache.infra.passes.options._
import at.forsyte.apalache.io.json.impl.DefaultTagReader
import at.forsyte.apalache.tla.bmcmt.config.TraceeModule
import at.forsyte.apalache.tla.tracee.UJsonTraceReader
import org.backuity.clist._

import java.io.File

/**
 * This command initiates the 'tracee' command line.
 *
 * TODO: Instead of extending Check, make both Check and Tracee extend common trait (#2245)
 *
 * @author
 *   Jure Kukovec
 */
class TraceeCmd(name: String = "tracee", description: String = "Evaluate expressions over a trace.")
    extends CheckCmd(name, description) {

  var trace: File = arg[File](description = "a file containing an ITF trace. Must also define --expressions.")

  var expressions: List[String] =
    arg[List[String]](name = "expressions",
        description = "TLA+ expressions to be evaluated over a given trace. Must also define --trace.")

  private val traceReader = new UJsonTraceReader(None, DefaultTagReader)

  private def getLenFromFile(file: File): Int = {
    val fileSrc = FileSource(file)
    val ujson = traceReader.read(fileSrc)
    traceReader.getTraceLength(ujson)
  }

  // Creates a tuning regex for search.transitionFilter
  private def tuningRegexFromLength(len: Int): String =
    ("0->0" +: (1 until len)
      .map { i =>
        // Because the 0th transition goes into the initial state, the
        // i-th transition overall uses the next-transition labeled with i-1
        s"$i->${i - 1}"
      }).mkString("|")

  // Can't pass tuning via flags
  override def collectTuningOptions(): Map[String, String] = {
    val txFilter = tuningRegexFromLength(getLenFromFile(trace))

    Map(
        "search.outputTraces" -> "true",
        "search.transitionFilter" -> txFilter,
    )
  }

  override def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithTracee(cfg).get

    // The execution length is read from the input and is 1 shorter than the trace length,
    // because the trace contains the initial state.
    val executionLength = getLenFromFile(trace) - 1

    val lenAdjustedOpt = options.copy(checker = options.checker.copy(length = executionLength))
    PassChainExecutor.run(new TraceeModule(lenAdjustedOpt)) match {
      case Right(_)      => Right(s"Trace successfully generated.")
      case Left(failure) => Left(failure.exitCode, "Trace evaluation has found an error")
    }
  }

  override def toConfig(): Config.ApalacheConfig = {
    val cfg = super.toConfig()
    cfg.copy(
        tracee = cfg.tracee.copy(
            trace = Some(FileSource(trace)),
            expressions = Some(expressions),
        )
    )
  }

}
