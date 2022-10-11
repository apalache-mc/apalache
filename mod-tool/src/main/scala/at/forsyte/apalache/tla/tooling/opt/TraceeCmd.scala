package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.options._
import at.forsyte.apalache.tla.bmcmt.config.TraceeModule
import org.backuity.clist._

import java.io.File

/**
 * This command initiates the 'tracee' command line.
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

  private var persistentLen: Int = 0 // hack

  // TODO: Guards and checks
  def getLenFromFile(file: File): Int = {
    val json = ujson.read(file)
    json("states").arr.length
  }

  // Can't pass tuning via flags
  override def collectTuningOptions(): Map[String, String] = {

    val len = getLenFromFile(trace)
    persistentLen = len - 1 // 1st state is init, len-1 transitions

    val txFilter = ("0->0" +: (1 until len)
      .map { i =>
        s"$i->${i - 1}" // -1, since the 1st state is init
      }).mkString("|")

    Map(
        "search.outputTraces" -> "true",
        "search.transitionFilter" -> txFilter,
    )
  }

  override def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithTracee(cfg).get

    val lenAdjustedOpt = options.copy(checker = options.checker.copy(length = persistentLen))
    PassChainExecutor.run(new TraceeModule(lenAdjustedOpt)) match {
      // TODO: update this for traces
      case Right(_)      => Right(s"Checker reports no error up to computation length ${options.checker.length}")
      case Left(failure) => Left(failure.exitCode, "Checker has found an error")
    }
  }

  override def toConfig(): Config.ApalacheConfig = {
    val cfg = super.toConfig()
    cfg.copy(
        tracee = cfg.tracee.copy(
            trace = Some(trace),
            expressions = Some(expressions),
        )
    )
  }

}
