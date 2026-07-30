package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.ExitCodes
import at.forsyte.apalache.tla.lir.Feature

import java.io.File
import org.backuity.clist._
import org.backuity.clist.util.Read
import at.forsyte.apalache.io.config.{ApalacheConfig, CommonPatch, ConfigParseResult, RunContextPatch}
import com.typesafe.scalalogging.LazyLogging

import scala.annotation.tailrec

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
  protected final val configDefaults: ApalacheConfig = ApalacheConfig.defaults

  /** Append a consistently formatted default obtained from its authoritative source. */
  protected final def descriptionWithDefault(description: String, default: Any): String =
    s"$description, default: ${renderDefault(default)}"

  @tailrec
  private def renderDefault(default: Any): String =
    default match {
      case None => "none"
      case Some(value) => renderDefault(value)
      case values: Iterable[_] if values.isEmpty => "none"
      case values: Iterable[_] => values.mkString(",")
      case value => value.toString
    }

  private val displayedDefaultOutDir = s"./${configDefaults.common.outDir.get.getFileName}"

  var configFile: Option[File] = opt[Option[File]](description = descriptionWithDefault(
    "strict JSON configuration to read. Overrides local .apalache.json files",
    configDefaults.context.configFile,
  ) + " (overrides envvar CONFIG_FILE)",
      useEnv = true)
  var debug: Option[Boolean] = opt[Option[Boolean]](
    description = descriptionWithDefault(
      "extensive logging in detailed.log and log.smt",
      configDefaults.common.debug,
    ))
  var smtprof: Option[Boolean] = opt[Option[Boolean]](
    description = descriptionWithDefault(
      "profile SMT constraints in profile.csv",
      configDefaults.common.smtprof,
    ))
  var profiling: Option[Boolean] = opt[Option[Boolean]](description = descriptionWithDefault(
    "write general profiling data to profile-rules.txt in the run directory",
    configDefaults.common.profiling,
  ) + " (overrides envvar PROFILING)",
      useEnv = true)
  var outDir: Option[File] = opt[Option[File]](
    description = descriptionWithDefault(
      "where all output files will be written",
      displayedDefaultOutDir,
    ) + " (overrides envvar OUT_DIR)",
      useEnv = true)
  var runDir: Option[File] = opt[Option[File]](description = descriptionWithDefault(
    "additional directory wherein output files for this run will be written directly",
    configDefaults.common.runDir,
  ) + " (overrides envvar RUN_DIR)",
      useEnv = true)
  var writeIntermediate: Option[Boolean] = opt[Option[Boolean]](description = descriptionWithDefault(
    "write intermediate output files to `out-dir`",
    configDefaults.common.writeIntermediate,
  ) + " (overrides envvar WRITE_INTERMEDIATE)",
      useEnv = true)
  var features: Option[Seq[Feature]] = opt[Option[Seq[Feature]]](default = None,
      description = {
        val featureDescriptions: Seq[String] = Feature.all.map(f => s"  * ${f.name}: ${f.description}")
        val header = descriptionWithDefault(
          "a comma-separated list of experimental features",
          configDefaults.common.features,
        ) + ":"
        (header +: featureDescriptions).mkString("\n")
      })

  /** Build the sparse top-level configuration supplied by this command line. */
  def toConfig: ConfigParseResult[ApalacheConfig] = {
    logger.info("Loading configuration")

    ConfigParseResult.success(ApalacheConfig(
      context = RunContextPatch(
        command = Some(name),
        configFile = configFile.map(_.toPath),
      ),
      common = CommonPatch(
        outDir = outDir.map(_.toPath),
        runDir = runDir.map(_.toPath),
        debug = debug,
        smtprof = smtprof,
        profiling = profiling,
        writeIntermediate = writeIntermediate,
        features = features.map(_.toList),
      ),
    ))
  }

  /**
   * Run the process corresponding to the specified subcommand
   *
   * All execution logic specific to the subcommand should be encapsulated in the [[run]] method.
   *
   * Most subclasses use the `PassChainExecutor` to sequence a chain of passes. `PassChainExecutor`s are created by
   * providing a `ToolModule`. E.g.,
   *
   * @param config
   * The merged configuration produced after parsing the command line.
   * @return
   *   `Right(msg)` on a successful execution or `Left((errCode, msg))` if the process fails, where `errCode` is the
   *   return code with the which the program will be terminated. In either case `msg` is the final message reported to
   *   the user.
   */
  def run(config: ApalacheConfig): Either[(ExitCodes.TExitCode, String), String]

  private var _invocation = ""
  private var _env = ""

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
  // If the flag is not given and no default is specified in the declaration,
  // clist defaults to None.
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

  /** Merge a higher-precedence command patch into a successfully constructed base configuration. */
  final protected def mergeConfig(
                                   base: ConfigParseResult[ApalacheConfig],
                                   higher: ApalacheConfig): ConfigParseResult[ApalacheConfig] = {
    if (base.isSuccess) {
      ConfigParseResult.success(higher.mergeWithLower(base.requireValue()), base.warnings)
    } else {
      ConfigParseResult.failureFrom(base)
    }
  }

  final protected def runWithOptions[A](
                                         result: ConfigParseResult[A]
                                       )(body: A => Either[(ExitCodes.TExitCode, String), String]): Either[(ExitCodes.TExitCode, String), String] = {
    result.warnings.foreach(warning => logger.warn(warning))
    if (result.isSuccess) body(result.requireValue())
    else Left(ExitCodes.ERROR -> result.errors.mkString("Configuration error: ", "; ", ""))
  }

  override def read(args: List[String]): Unit = {
    _env = super.options
      .filter(_.useEnv.getOrElse(false))
      .flatMap(getOptionEnvVar)
      .mkString(" ")

    _invocation = args.mkString(" ")

    super.read(args)
  }
}
