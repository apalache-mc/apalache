package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import at.forsyte.apalache.infra.PassOptionException
import at.forsyte.apalache.io.config.SMTEncoding
import at.forsyte.apalache.io.config.SMTSolver
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import org.apache.commons.configuration2.builder.fluent.Configurations
import org.apache.commons.configuration2.ex.ConfigurationException
import org.backuity.clist._
import org.backuity.clist.util.Read

import java.io.{File, FileNotFoundException}
import scala.jdk.CollectionConverters._
import at.forsyte.apalache.io.config.{ApalacheConfig, ApalacheConfigResolver, CheckerPatch, ConfigParseResult}
import at.forsyte.apalache.io.tuning.FineTuningParser
import org.apache.commons.io.FilenameUtils
import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.io.config.Algorithm
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams

/**
 * This command initiates the 'check' command line.
 *
 * @author
 *   Igor Konnov
 */
class CheckCmd(name: String = "check", description: String = "Check a TLA+ specification")
    extends AbstractCheckerCmd(name, description) {

  // Parses the smtEncoding option
  implicit val smtEncodingRead: Read[SMTEncoding] =
    Read.reads[SMTEncoding](s"an SMT encoding: ${SMTEncoding.values.mkString(", ")}")(SMTEncoding.fromString)

  // Parses the smtSolver option
  implicit val smtSolverRead: Read[SMTSolver] =
    Read.reads[SMTSolver](s"an SMT solver backend: ${SMTSolver.values.mkString(", ")}")(SMTSolver.fromString)

  // Parses the algo option
  implicit val algoRead: Read[Algorithm] =
    Read.reads[Algorithm](s"a checking algorithm: ${Algorithm.values.mkString(", ")}")(Algorithm.fromString)

  var algo: Option[Algorithm] = opt[Option[Algorithm]](name = "algo", default = None,
      description = descriptionWithDefault(
          s"the search algorithm: ${Algorithm.values.map(_.displayName).mkString(", ")}",
          configDefaults.checker.algorithm,
      ))
  var smtEncoding: Option[SMTEncoding] = opt[Option[SMTEncoding]](name = "smt-encoding", useEnv = true, default = None,
      description = descriptionWithDefault(
          s"the SMT encoding: ${SMTEncoding.values.map(_.displayName).mkString(", ")}",
          configDefaults.checker.smtEncoding,
      ) + " (overrides envvar SMT_ENCODING)")
  var smtSolver: Option[SMTSolver] = opt[Option[SMTSolver]](name = "smt-solver", useEnv = true, default = None,
      description = descriptionWithDefault(
          s"the SMT solver backend: ${SMTSolver.values.map(_.displayName).mkString(", ")}",
          configDefaults.checker.smtSolver,
      ) + " (overrides envvar SMT_SOLVER)")
  var tuningOptionsFile: Option[String] =
    opt[Option[String]](name = "tuning-options-file", default = None,
        description = descriptionWithDefault(
            "filename of the tuning options, see docs/tuning.md",
            configDefaults.checker.tuning,
        ))
  var tuningOptions: Option[String] =
    opt[Option[String]](name = "tuning-options", default = None,
        description = descriptionWithDefault(
            "tuning options as arguments in the format key1=val1:key2=val2:key3=val3 (priority over --tuning-options-file)",
            configDefaults.checker.tuning,
        ))
  var discardDisabled: Option[Boolean] = opt[Option[Boolean]](name = "discard-disabled", default = None,
      description = descriptionWithDefault(
          "pre-check, whether a transition is disabled, and discard it, to make SMT queries smaller",
          configDefaults.checker.discardDisabled,
      ))
  var noDeadlocks: Option[Boolean] =
    opt[Option[Boolean]](name = "no-deadlock", default = None,
        description = descriptionWithDefault(
            "do not check for deadlocks",
            !ApalacheConfigResolver.defaultCheckDeadlocks,
        ))

  var maxError: Option[Int] =
    opt[Option[Int]](name = "max-error",
        description = descriptionWithDefault(
            "do not stop on first error, but produce at most the given number of errors (requires --view when greater than 1)",
            configDefaults.checker.maxError,
        ), default = None)

  var view: Option[String] =
    opt[Option[String]](name = "view",
        description = descriptionWithDefault(
            "the state view to use with --max-error=n",
            configDefaults.checker.view,
        ), default = None)

  var saveRuns: Option[Boolean] =
    opt[Option[Boolean]](name = "output-traces",
        description = descriptionWithDefault(
            "save an example trace for each symbolic run",
            ModelCheckerParams.defaultOutputTraces,
        ), default = None)

  var timeoutSmtSec: Option[Int] =
    opt[Option[Int]](name = "timeout-smt",
        description = descriptionWithDefault(
            "limit the duration of a single SMT check query with `n` seconds",
            configDefaults.checker.timeoutSmtSeconds,
        ) + " (unlimited)", default = None)

  override def toConfig: ConfigParseResult[ApalacheConfig] = {
    val combinedTuningOptions =
      try {
        val loadedTuningOptions = tuningOptionsFile.map(f => loadProperties(f)).getOrElse(Map())
        val outputTraceOptions = saveRuns match {
          case Some(value) => Map("search.outputTraces" -> value.toString)
          case None        => Map.empty
        }
        overrideProperties(loadedTuningOptions, tuningOptions.getOrElse("")) ++ outputTraceOptions
      } catch {
        case e: PassOptionException => return ConfigParseResult.failure(e.getMessage)
      }

    val base = super.toConfig
    if (!base.isSuccess) return ConfigParseResult.failureFrom(base)

    val tuning =
      if (combinedTuningOptions.nonEmpty) Some(combinedTuningOptions)
      else None
    val merged = mergeConfig(
        base,
        ApalacheConfig(
            checker = CheckerPatch(
                algorithm = algo,
                smtSolver = smtSolver,
                smtEncoding = smtEncoding,
                tuning = tuning,
                discardDisabled = discardDisabled,
                checkDeadlocks = noDeadlocks.map(value => !value),
                maxError = maxError,
                timeoutSmtSeconds = timeoutSmtSec,
                view = view,
            )
        ),
    )

    warnIfTLCConfigIsPresent(merged.requireValue())
    merged
  }

  private def warnIfTLCConfigIsPresent(cfg: ApalacheConfig): Unit = {
    // The older versions of apalache were loading a TLC config file of
    // the same basename as the spec by default. We have flipped this
    // behavior in version 0.25.0. Hence, warn the user that their config
    // is not loaded by default.
    cfg.source.foreach {
      // The check is only relevant for TLA files
      case InputSource.FileSource(path, InputSource.Format.Tla) =>
        if (cfg.checker.tlcConfig.isEmpty) {
          val stem = FilenameUtils.removeExtension(path.getFileName.toString)
          val defaultConfig = new File(stem + ".cfg")
          if (defaultConfig.exists()) {
            val msg =
              s"  > TLC config file found in specification directory. To enable it, pass --config=$defaultConfig."
            logger.info(msg)
          }
        }
      case _ => ()
    }

  }

  override def run(config: ApalacheConfig): Either[(TExitCode, String), String] = {
    runWithOptions(ApalacheConfigResolver.resolveCheck(config)) { options =>
      val tuning = options.checker.tuning
      logger.info("Tuning: " + tuning.toList.map { case (k, v) => s"$k=$v" }.mkString(":"))

      PassChainExecutor(new CheckerModule(options)).run() match {
        case Right(_)      => Right(s"Checker reports no error up to computation length ${options.checker.length}")
        case Left(failure) => Left(failure.exitCode, "Checker has found an error")
      }
    }
  }

  private def loadProperties(filename: String): Map[String, String] = {
    // use an apache-commons library, as it supports variable substitution
    try {
      val config = new Configurations().properties(new File(filename))
      // access configuration properties
      var map = Map[String, String]()
      for (name: String <- config.getKeys.asScala) {
        map += (name -> config.getString(name))
      }
      // parse the properties and convert them back to strings for config serialization
      FineTuningParser.fromStrings(map) match {
        case Right(parsed) => parsed.view.mapValues(_.toString).toMap
        case Left(error)   => throw new PassOptionException(s"Error in the properties file $filename: $error")
      }
    } catch {
      case _: FileNotFoundException =>
        throw new PassOptionException(s"The properties file $filename not found")

      case e: ConfigurationException =>
        throw new PassOptionException(s"Error in the properties file $filename: ${e.getMessage}")
    }
  }

  private def overrideProperties(props: Map[String, String], propsAsString: String): Map[String, String] = {
    def parseKeyValue(text: String): (String, String) = {
      val parts = text.split('=')
      if (parts.length != 2 || parts.head.trim == "" || parts(1) == "") {
        throw new PassOptionException(s"Expected key=value in --tuning-options=$propsAsString")
      } else {
        // trim to remove surrounding whitespace from the key, but allow the value to have white spaces
        (parts.head.trim, parts(1))
      }
    }

    val hereProps = {
      if (propsAsString.trim.nonEmpty) {
        // parse the properties and convert them back to strings for config serialization
        FineTuningParser.fromStrings(propsAsString.split(':').map(parseKeyValue).toMap) match {
          case Right(parsed) => parsed.view.mapValues(_.toString).toMap
          case Left(error)   => throw new PassOptionException(s"Error in the properties string $propsAsString: $error")
        }
      } else {
        Map.empty
      }
    }
    // hereProps may override the values in props
    props ++ hereProps
  }
}
