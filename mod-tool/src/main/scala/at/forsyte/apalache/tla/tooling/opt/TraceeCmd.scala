package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.options._
import at.forsyte.apalache.io.json.JsonDeserializationError
import at.forsyte.apalache.io.json.impl.{UJsonRep, UJsonScalaFactory}
import at.forsyte.apalache.tla.bmcmt.config.TraceeModule
import org.backuity.clist._

import java.io.File
import scala.util.{Failure, Success, Try}

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

  // If we set the --length inside collectTuningOptions it gets overwritten later.
  // therefore, we store it locally, and only update the options right before calling run()
  private var persistentLen: Int = 0

  def getLenFromFile(file: File): Int = Try(UJsonRep(ujson.read(file))) match {
    case Success(json) =>
      // ITF case
      val statesOpt = json.getFieldOpt("states").map(UJsonScalaFactory.asSeq)
      statesOpt match {
        case Some(seq) => seq.length
        case None      =>
          // generic case
          val declOpt = for {
            modules <- json.getFieldOpt("modules")
            decls <- UJsonScalaFactory.asSeq(modules).head.getFieldOpt("declarations")
          } yield UJsonScalaFactory.asSeq(decls)

          // we need len-2 for CInit (head) and Inv (last)
          declOpt.map(_.length - 2).getOrElse {
            throw new JsonDeserializationError(s"${file.getCanonicalPath} is malformed.")
          }
      }
    case Failure(exception) =>
      throw new JsonDeserializationError(s"Could not read ${file.getCanonicalPath}.", exception)
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
      case Right(_)      => Right(s"Trace successfully generated.")
      case Left(failure) => Left(failure.exitCode, "Trace evaluation has found an error")
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
