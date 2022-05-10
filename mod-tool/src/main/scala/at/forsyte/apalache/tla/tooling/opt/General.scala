package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.io.CliConfig
import at.forsyte.apalache.tla.lir.{Feature, RowsFeature}

import java.io.File
import org.backuity.clist._
import org.backuity.clist.util.Read

/**
 * The general commands.
 *
 * See: https://github.com/backuity/clist
 *
 * @author
 *   Igor Konnov
 */
trait General extends Command with CliConfig {
  // TODO Fix excessively long strings
  var configFile = opt[Option[File]](description =
        "configuration to read from (JSON and HOCON formats supported). Overrides any local .aplache.cfg files. (overrides envvar CONFIG_FILE)",
      useEnv = true)
  var debug = opt[Boolean](description = "extensive logging in detailed.log and log.smt, default: false")
  var smtprof = opt[Boolean](description = "profile SMT constraints in profile.csv, default: false")
  var profiling = opt[Option[Boolean]](description =
        s"write general profiling data to profile-rules.txt in the run directory, default: false (overrides envvar PROFILING)",
      useEnv = true)
  var outDir = opt[Option[File]](
      description = "where all output files will be written, default: ./_apalache-out (overrides envvar OUT_DIR)",
      useEnv = true)
  var runDir = opt[Option[File]](description =
        "additional directory wherein output files for this run will be written directly, default: none (overrides envvar RUN_DIR)",
      useEnv = true)
  var writeIntermediate = opt[Option[Boolean]](description =
        "write intermediate output files to `out-dir`, default: false (overrides envvar WRITE_INTERMEDIATE)",
      useEnv = true)
  var features = opt[Seq[Feature]](default = Seq(),
      description = """a comma-separated list of experimental features:
        | - rows: enable row typing as explained in ADR-014
        |""".stripMargin)

  private var _invocation = ""
  private var _env = ""

  // Parse a feature
  implicit def featureRead: Read[Feature] = {
    Read.reads[Feature]("a feature: rows") {
      case "rows"     => RowsFeature()
      case unexpected => throw new IllegalArgumentException(s"Unexpected feature: $unexpected")
    }
  }

  implicit def featureSeqRead: Read[Seq[Feature]] = {
    Read.reads[Seq[Feature]](expecting = "a comma-separated list of features: rows") { str =>
      str.split(",").map(featureRead.reads)
    }
  }

  private def getOptionEnvVar(option: CliOption[_]): Option[String] = {
    val envVar = option.name.replace("-", "_").toUpperCase()
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
