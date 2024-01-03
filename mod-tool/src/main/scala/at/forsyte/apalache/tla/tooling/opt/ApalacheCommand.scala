package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.ExitCodes
import at.forsyte.apalache.tla.lir.Feature

import java.io.File
import org.backuity.clist._
import org.backuity.clist.util.Read
import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.io.ConfigManager
import com.typesafe.scalalogging.LazyLogging
import scala.util.Try
import scala.util.Failure
import at.forsyte.apalache.io.ConfigurationError

/**
 * The base class used by all Apalache CLI subcommands.
 *
 * See: https://github.com/backuity/clist
 *
 * @author
 *   Igor Konnov, Shon Feder
 */
abstract class ApalacheCommand(name: String, description: String)
    extends Command(name: String, description: String) with LazyLogging {
  // TODO Fix excessively long strings
  var configFile = opt[Option[File]](description =
        "configuration to read from (JSON and HOCON formats supported). Overrides any local .aplache.cfg files. (overrides envvar CONFIG_FILE)",
      useEnv = true)
  var debug = opt[Option[Boolean]](description = "extensive logging in detailed.log and log.smt, default: false")
  var smtprof = opt[Option[Boolean]](description = "profile SMT constraints in profile.csv, default: false")
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
  var features = opt[Option[Seq[Feature]]](default = None,
      description = {
        val featureDescriptions: Seq[String] = Feature.all.map(f => s"  * ${f.name}: ${f.description}")
        ("a comma-separated list of experimental features:" +: featureDescriptions).mkString("\n")
      })

  /**
   * Derives an instance of [[at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig ApalacheConfig]] from the
   * command line arguments
   *
   * Any configuration values that determine program behavior outside of the class implementing the command line praser
   * instance should be communicated through the derived `ApalacheConfig`.
   */
  def toConfig(): Try[Config.ApalacheConfig] = {
    logger.info("Loading configuration")

    // We start with an *empty* base config, so that any values which are *not*
    // set by the CLI will be `None`.  This is required to allow the configs
    // derived from the CLI to override the configs from other source, while
    // still letting other config values that are not overriden to propagate
    // through.
    val cfg = Config.ApalacheConfig().empty
    Try(cfg.copy(common = cfg.common.copy(
            command = Some(name),
            configFile = configFile,
            debug = debug,
            smtprof = smtprof,
            profiling = profiling,
            outDir = outDir,
            runDir = runDir,
            writeIntermediate = writeIntermediate,
            features = features,
        )))
  }

  /**
   * Run the process corresponding to the specified subcommand
   *
   * All execution logic specific to the subcommand should be triggered encapsulated in the [[run]] method.
   *
   * Most subclasses use the `PassChainExecutor` to sequence a chain of passes. `PassChainExecutor`s are created by
   * providing a `ToolModule`. E.g.,
   *
   * {{{
   * import at.forsyte.apalache.infra.passes.PassChainExecutor
   * import at.forsyte.apalache.infra.passes.options.OptionGroup
   *
   * val options = OptionGroup.WithOutput(configuration)
   *
   * PassChainExecutor.run(new TypeCheckerModule(options)) match {
   *   case Right(module) => Right("Success msg")
   *   case Left(errCode) => Left(errorCode, "Failure msg")
   * }
   * }}}
   *
   * @return
   *   `Right(msg)` on a successful execution or `Left((errCode, msg))` if the process fails, where `errCode` is the
   *   return code with the which the program will be terminated. In either case `msg` is the final message reported to
   *   the user.
   */
  def run(): Either[(ExitCodes.TExitCode, String), String]

  private var _invocation = ""
  private var _env = ""
  private var _configure: Try[Config.ApalacheConfig] =
    Failure(new ConfigurationError("ApalacheCommand was never configured"))

  // A comma separated name of supported features
  private val featureList = Feature.all.map(_.name).mkString(", ")

  // Parse a feature
  implicit def featureRead: Read[Feature] = {
    Read.reads[Feature](s"a feature: ${featureList}") { str =>
      Feature.fromString(str).getOrElse(throw new IllegalArgumentException(s"Unexpected feature: ${str}"))
    }
  }

  implicit def featureSeqRead: Read[Seq[Feature]] = {
    Read.reads[Seq[Feature]](expecting = s"a comma-separated list of features: ${featureList}") { str =>
      str.split(",").map(featureRead.reads).toIndexedSeq
    }
  }

  // Improve parsing of "Option[Boolean]" flags so that flags of type `opt[Option[Boolean]]` can
  // be supplied without an explicit argument, like `--foo` instead of requiring `--foo=true`
  // If the flag is "not" given and no default is specified in the declaration of the cli flag, then clist defaults to "None".
  //
  // This enables to us read CLI boolean flags using the usual syntax, but also
  // to differentiate whether the user supplied a value. The latter information
  // allows us to use the CLI flags as possible overrides for configurations
  // loaded from other sources.
  implicit def optionBoolRead: Read[Option[Boolean]] =
    Read.reads[Option[Boolean]](expecting = "a boolean, such as 'true', 'yes', '1' or 'false', 'no', '0'") {
      // If "" is supplied, the user gave the flag with no argument
      case "" | "true" | "yes" | "1" => Some(true)
      case "false" | "no" | "0"      => Some(false)
    }

  implicit def listStringRead: Read[List[String]] =
    Read.reads[List[String]](expecting = "A comma separated list of strings, such as 'foo,bar,baz'")(
        _.split(",").toList)

  private def getOptionEnvVar(option: CliOption[_]): Option[String] = {
    val envVar = option.name.replace("-", "_").toUpperCase()
    sys.env.get(envVar).map(value => s"${envVar}=${value}")
  }

  /** A verbatim representation of the command line arguments given when invoking the command */
  def invocation: String = _invocation

  /** CLI options that are set through environment variables */
  def env: String = _env

  /**
   * The application configuration, derived by loading all configuration sources, concluding with the CLI options
   *
   * See [[at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig ApalacheConfig]] for details.
   */
  def configuration: Try[Config.ApalacheConfig] = _configure

  override def read(args: List[String]) = {
    _env = super.options
      .filter(_.useEnv.getOrElse(false))
      .flatMap(getOptionEnvVar)
      .mkString(" ")

    _invocation = args.mkString(" ")

    super.read(args)

    // Load configuration and merge in cli config
    // This must be invoked after we parse the CLI args
    _configure = this.toConfig().flatMap(ConfigManager(_))
  }
}
