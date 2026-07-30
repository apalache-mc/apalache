package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.InputSource.FileSource
import at.forsyte.apalache.io.config.Constants.{EXPRESSIONS, TRACE, TRACEE}
import at.forsyte.apalache.io.config._
import at.forsyte.apalache.io.json.DefaultTagJsonReader
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
class TraceeCmd(name: String = TRACEE, description: String = "Evaluate expressions over a trace.")
    extends CheckCmd(name, description) {

  var trace: File =
    arg[File](name = TRACE, description = "a file containing an ITF trace. Must also define --expressions.")

  var expressions: List[String] =
    arg[List[String]](name = EXPRESSIONS,
        description = "TLA+ expressions to be evaluated over a given trace. Must also define --trace.")

  private val traceReader = new UJsonTraceReader(None, DefaultTagJsonReader)

  private def getLenFromFile(src: InputSource): Int = {
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

  override def run(config: ApalacheConfig): Either[(TExitCode, String), String] = {
    runWithOptions(ApalacheConfigResolver.resolveTrace(config)) { options =>
      // The execution length is read from the input and is 1 shorter than the trace length,
      // because the trace contains the initial state.
      val executionLength = getLenFromFile(options.source) - 1
      val lenAdjustedOptions = options.withLength(executionLength)
      PassChainExecutor(new TraceeModule(lenAdjustedOptions)).run() match {
        case Right(_)      => Right("Trace successfully generated.")
        case Left(failure) => Left(failure.exitCode, "Trace evaluation has found an error")
      }
    }
  }

  override def toConfig: ConfigParseResult[ApalacheConfig] = {
    val base = super.toConfig
    if (!base.isSuccess) return ConfigParseResult.failureFrom(base)
    val source = FileSource(trace)
    if (!source.isSuccess) return ConfigParseResult.failureFrom(source)

    val src = source.requireValue()
    val tuning = Map(
        "search.outputTraces" -> "true",
        "search.transitionFilter" -> tuningRegexFromLength(getLenFromFile(src)),
    )
    mergeConfig(
        base,
        ApalacheConfig(
            checker = CheckerPatch(tuning = Some(tuning)),
            traceEvaluation = TraceEvaluationPatch(
                trace = Some(src),
                expressions = Some(expressions),
            ),
        ),
    )
  }

}
