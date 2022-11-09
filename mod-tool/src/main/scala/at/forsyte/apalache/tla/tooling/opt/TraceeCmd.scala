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

  private def getLenFromFile(src: SourceOption): Int = {
    val ujson = traceReader.read(src)
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

  override def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithTracee(cfg).get

    // The execution length is read from the input and is 1 shorter than the trace length,
    // because the trace contains the initial state.
    val executionLength = getLenFromFile(options.input.source) - 1

    val lenAdjustedOpt = options.copy(checker = options.checker.copy(length = executionLength))
    PassChainExecutor.run(new TraceeModule(lenAdjustedOpt)) match {
      case Right(_)      => Right(s"Trace successfully generated.")
      case Left(failure) => Left(failure.exitCode, "Trace evaluation has found an error")
    }
  }

  override def toConfig() = for {
    cfg <- super.toConfig()
    src <- FileSource(trace)
    tuning = Some(Map(
            "search.outputTraces" -> "true",
            "search.transitionFilter" -> tuningRegexFromLength(getLenFromFile(src)),
        ))
  } yield cfg.copy(
      checker = cfg.checker.copy(tuning = tuning),
      tracee = cfg.tracee.copy(
          trace = Some(src),
          expressions = Some(expressions),
      ),
  )

}
