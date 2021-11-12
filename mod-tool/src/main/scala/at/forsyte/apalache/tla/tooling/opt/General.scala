package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.io.{OutputManagerConfig, OutputManager}

import java.io.File
import org.backuity.clist._
import at.forsyte.apalache.io.OutputManager

/**
 * The general commands.
 *
 * See: https://github.com/backuity/clist
 *
 * @author Igor Konnov
 */
trait General extends Command with OutputManagerConfig {

  var debug = opt[Boolean](description = "extensive logging in detailed.log and log.smt, default: false")
  var smtprof = opt[Boolean](description = "profile SMT constraints in log.smt, default: false")
  var profiling = opt[Option[Boolean]](name = OutputManager.Names.ProfilingFlag,
      description =
        s"write general profiling data to profile-rules.txt in the run directory, default: false (overrides envvar PROFILING)",
      useEnv = true)
  var outDir = opt[Option[File]](name = OutputManager.Names.OutdirNameInCfg,
      description = "where all output files will be written, default: ./_apalache-out (overrides envvar OUT_DIR)",
      useEnv = true)
  var runDir = opt[Option[File]](
      description =
        "additional directory wherein output files for this run will be written directly, default: none (overrides envvar RUN_DIR)",
      useEnv = true)
  var writeIntermediate = opt[Option[Boolean]](name = OutputManager.Names.IntermediateFlag,
      description =
        "write intermediate output files to `out-dir`, default: false (overrides envvar WRITE_INTERMEDIATE)",
      useEnv = true)

  private var _invocation = ""
  private var _env = ""

  private def getOptionEnvVar(option: CliOption[_]): Option[String] = {
    var envVar = option.name.replace("-", "_").toUpperCase()
    sys.env.get(envVar).map(value => s"${envVar}=${value}")
  }

  /** A verbatim representation of the command line arguments given when invoking the command */
  def invocation: String = _invocation

  /** CLI options that are set through environment variables */
  def env: String = _env

  override def read(args: List[String]) = {
    _env = super.options
      .filter(_.useEnv.getOrElse(false))
      .flatMap(getOptionEnvVar)
      .mkString(" ")

    _invocation = args.mkString(" ")

    super.read(args)
  }
}
